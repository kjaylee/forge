pub struct Element {
    pub name: String,
    pub attr: Vec<(String, String)>,
    pub children: Vec<Element>,
    pub text: Option<String>,
}

impl Element {
    pub fn new(name: impl ToString) -> Self {
        Element {
            name: name.to_string(),
            attr: vec![],
            children: vec![],
            text: None,
        }
    }

    pub fn text(mut self, text: impl ToString) -> Self {
        self.text = Some(text.to_string());
        self
    }

    pub fn attr(mut self, key: impl ToString, value: impl ToString) -> Self {
        self.attr.push((key.to_string(), value.to_string()));
        self
    }

    pub fn append(mut self, children: impl IntoIterator<Item = Element>) -> Self {
        for c in children {
            self.children.push(c);
        }
        self
    }

    pub fn render(&self) -> String {
        let mut result = String::new();

        result.push_str(&format!("<{}", self.name));
        for (key, value) in &self.attr {
            result.push_str(&format!(" {}=\"{}\"", key, value));
        }
        result.push('>');

        if let Some(ref text) = self.text {
            result.push_str(text);
        }

        for child in &self.children {
            result.push_str(&child.render());
        }
        result.push_str(&format!("</{}>", self.name));
        result
    }
}

pub struct ElementIterator(Option<Element>);
impl Iterator for ElementIterator {
    type Item = Element;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.take()
    }
}

impl IntoIterator for Element {
    type Item = Element;
    type IntoIter = ElementIterator;
    fn into_iter(self) -> Self::IntoIter {
        ElementIterator(Some(self))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_element() {
        let html = Element::new("div");
        let actual = html.render();
        let expected = "<div></div>";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_element_with_attributes() {
        let html = Element::new("div").attr("class", "test");
        let actual = html.render();
        let expected = "<div class=\"test\"></div>";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_element_with_children() {
        let html = Element::new("div")
            .attr("class", "test")
            .append(Element::new("span"));
        let actual = html.render();
        let expected = "<div class=\"test\"><span></span></div>";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_element_with_multiple_children() {
        let html = Element::new("div")
            .attr("class", "test")
            .append(vec![Element::new("span"), Element::new("p")]);
        let actual = html.render();
        let expected = "<div class=\"test\"><span></span><p></p></div>";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_element_with_nested_children() {
        let html = Element::new("div").attr("class", "test").append(vec![
            Element::new("span").attr("class", "child"),
            Element::new("p").attr("class", "child"),
        ]);
        let actual = html.render();
        let expected =
            "<div class=\"test\"><span class=\"child\"></span><p class=\"child\"></p></div>";
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_element_with_text() {
        let html = Element::new("div")
            .attr("class", "test")
            .text("Hello, world!")
            .append(vec![Element::new("span").attr("class", "child")]);
        let actual = html.render();
        let expected = "<div class=\"test\">Hello, world!<span class=\"child\"></span></div>";
        assert_eq!(actual, expected);
    }
}
