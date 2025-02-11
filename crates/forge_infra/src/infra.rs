use forge_app::Infrastructure;
use forge_domain::ModelId;

use crate::env::{ForgeEnvironmentService, TestEnvironmentService};
use crate::file_read::ForgeFileReadService;

pub struct ForgeInfra {
    _file_read_service: ForgeFileReadService,
    _environment_service: ForgeEnvironmentService,
}

impl ForgeInfra {
    pub fn new(restricted: bool) -> Self {
        Self {
            _file_read_service: ForgeFileReadService::new(),
            _environment_service: ForgeEnvironmentService::new(restricted),
        }
    }
}

impl Infrastructure for ForgeInfra {
    type EnvironmentService = ForgeEnvironmentService;
    type FileReadService = ForgeFileReadService;

    fn environment_service(&self) -> &Self::EnvironmentService {
        &self._environment_service
    }

    fn file_read_service(&self) -> &Self::FileReadService {
        &self._file_read_service
    }
}

pub struct TestInfra {
    _file_read_service: ForgeFileReadService,
    _environment_service: TestEnvironmentService,
}
impl TestInfra {
    pub fn new(large_model_id: ModelId, small_model_id: ModelId) -> Self {
        Self {
            _file_read_service: ForgeFileReadService::new(),
            _environment_service: TestEnvironmentService::new(large_model_id, small_model_id),
        }
    }
}
impl Infrastructure for TestInfra {
    type EnvironmentService = TestEnvironmentService;
    type FileReadService = ForgeFileReadService;

    fn environment_service(&self) -> &Self::EnvironmentService {
        &self._environment_service
    }

    fn file_read_service(&self) -> &Self::FileReadService {
        &self._file_read_service
    }
}
