use anyhow::Result;
use forge_template::Element;

#[cfg(test)]
use crate::FsCreateOutput;
use crate::error::Error;
use crate::operation::Operation;

pub struct ToolResultTransformer;

impl ToolResultTransformer {
    pub fn transform(result: Result<Operation>) -> Result<Operation> {
        match result {
            Ok(operation) => Ok(operation),
            Err(error) => {
                if let Some(app_error) = error.downcast_ref::<Error>() {
                    match app_error {
                        Error::FileExistsOverwriteRequired { original_path, temp_file_path } => {
                            let element = Element::new("error")
                                .attr("type", "file_exists_overwrite_required")
                                .attr("original_path", original_path)
                                .attr("temp_file_path", temp_file_path)
                                .append(
                                    Element::new("message").text(format!(
                                        "File already exists at '{original_path}'. A temporary file has been created at '{temp_file_path}'."
                                    ))
                                )
                                .append(
                                    Element::new("solution").text(format!(
                                        "To overwrite: move the file \"{temp_file_path}\" to \"{original_path}\""
                                    ))
                                )
                                .append(
                                    Element::new("alternative").text("Re-run the create operation with overwrite=true.")
                                );

                            Err(anyhow::anyhow!("{}", element.to_string()))
                        }
                        _ => Err(error),
                    }
                } else {
                    Err(error)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::anyhow;
    use forge_domain::{FSWrite, ToolName};
    use insta::assert_snapshot;

    use super::*;

    fn fixture_fs_write() -> FSWrite {
        FSWrite {
            path: "/test/path.txt".to_string(),
            content: "test content".to_string(),
            overwrite: false,
            explanation: None,
        }
    }

    #[test]
    fn test_transform_successful_operation() {
        let input = fixture_fs_write();
        let output = FsCreateOutput { path: input.path.clone(), before: None, warning: None };
        let operation = Operation::FsCreate { input, output };
        let fixture = Ok(operation);

        let actual = ToolResultTransformer::transform(fixture);

        assert!(actual.is_ok());
        let operation = actual.unwrap();
        assert_snapshot!(format!("{:?}", operation));
    }

    #[test]
    fn test_transform_file_exists_error() {
        let fixture = Err(anyhow!(Error::FileExistsOverwriteRequired {
            original_path: "/original/path.txt".to_string(),
            temp_file_path: "/tmp/temp_file.txt".to_string(),
        }));

        let actual = ToolResultTransformer::transform(fixture);

        assert!(actual.is_err());
        let error_message = actual.unwrap_err().to_string();
        assert_snapshot!(error_message);
    }

    #[test]
    fn test_transform_other_error() {
        let fixture = Err(anyhow!("Some other error"));

        let actual = ToolResultTransformer::transform(fixture);

        assert!(actual.is_err());
        let error_message = actual.unwrap_err().to_string();
        assert_snapshot!(error_message);
    }

    #[test]
    fn test_transform_other_app_error() {
        let fixture = Err(anyhow!(Error::NotFound(ToolName::new("missing_tool"))));

        let actual = ToolResultTransformer::transform(fixture);

        assert!(actual.is_err());
        let error_message = actual.unwrap_err().to_string();
        assert_snapshot!(error_message);
    }
}
