use nom::{
    bytes::complete::{tag, take_until1},
    character::complete::space0,
    error::{Error, ErrorKind},
    sequence::delimited,
    IResult,
};

#[derive(Debug, PartialEq)]
pub struct TagParser;

#[derive(Debug, PartialEq)]
enum ParsedTag {
    Tag { name: String, content: String },
}

#[derive(Debug)]
pub struct ParseResult(Vec<ParsedTag>);

impl ParseResult {
    pub fn get(&self, tag: &str) -> Option<&str> {
        self.0.iter().find_map(|t| match t {
            ParsedTag::Tag { name, content } if name == tag => Some(content.as_str()),
            _ => None,
        })
    }

    pub fn get_all(&self, tag: &str) -> Vec<&str> {
        self.0.iter().filter_map(|t| match t {
            ParsedTag::Tag { name, content } if name == tag => Some(content.as_str()),
            _ => None,
        }).collect()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl TagParser {
    fn parse_tag_name(input: &str) -> IResult<&str, &str, Error<&str>> {
        delimited(tag("<"), take_until1(">"), tag(">"))(input)
    }

    fn parse_tag_content<'a>(
        input: &'a str,
        tag_name: &str,
    ) -> IResult<&'a str, String, Error<&'a str>> {
        let close_tag = format!("</{}>", tag_name);
        let close_tag_str = close_tag.as_str();

        let parser_fn = take_until1::<&str, &str, Error<&str>>(close_tag_str);
        if let Ok((rest, content)) = parser_fn(input) {
            let (rest, _) = tag(close_tag_str)(rest)?;
            Ok((rest, content.trim().to_string()))
        } else {
            Err(nom::Err::Error(Error::new(input, ErrorKind::TakeUntil)))
        }
    }

    fn parse_complete_tag(input: &str) -> IResult<&str, ParsedTag, Error<&str>> {
        let (input, _) = space0(input)?;
        let (input, tag_name) = Self::parse_tag_name(input)?;
        let (input, content) = Self::parse_tag_content(input, tag_name)?;
        Ok((input, ParsedTag::Tag { name: tag_name.to_string(), content }))
    }

    pub fn parse(content: String) -> ParseResult {
        let mut tags = Vec::new();
        let mut remaining = content.as_str();

        while !remaining.is_empty() {
            if remaining.starts_with('<') {
                match Self::parse_complete_tag(remaining) {
                    Ok((rest, tag)) => {
                        tags.push(tag);
                        remaining = rest;
                    }
                    Err(_) => {
                        if let Some(pos) = remaining[1..].find('<') {
                            remaining = &remaining[pos + 1..];
                        } else {
                            break;
                        }
                    }
                }
            } else if let Some(pos) = remaining.find('<') {
                remaining = &remaining[pos..];
            } else {
                break;
            }
        }

        ParseResult(tags)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_tag() {
        let content = "<title>Hello World</title>";
        let result = TagParser::parse(content.to_string());
        assert_eq!(result.get("title"), Some("Hello World"));
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_parse_multiple_tags() {
        let content = "<title>First</title>Some text<desc>Description</desc>";
        let result = TagParser::parse(content.to_string());
        assert_eq!(result.get("title"), Some("First"));
        assert_eq!(result.get("desc"), Some("Description"));
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_get_all_tags() {
        let content = "<item>1</item><item>2</item><item>3</item>";
        let result = TagParser::parse(content.to_string());
        assert_eq!(result.get_all("item"), vec!["1", "2", "3"]);
    }
}
