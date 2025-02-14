use forge_app::{EnvironmentService, Infrastructure};

use crate::conn::ForgeConnection;
use crate::env::ForgeEnvironmentService;
use crate::file_read::ForgeFileReadService;
use crate::knowledge::ForgeKnowledgeRepository;

pub struct ForgeInfra {
    _file_read_service: ForgeFileReadService,
    _environment_service: ForgeEnvironmentService,
    _information_repo: ForgeKnowledgeRepository,
}

impl ForgeInfra {
    pub fn new(restricted: bool) -> Self {
        let _environment_service = ForgeEnvironmentService::new(restricted);

        let conn = ForgeConnection::new(_environment_service.get_environment());

        Self {
            _file_read_service: ForgeFileReadService::new(),
            _environment_service,
            _information_repo: ForgeKnowledgeRepository::new(conn),
        }
    }
}

impl Infrastructure for ForgeInfra {
    type EnvironmentService = ForgeEnvironmentService;
    type FileReadService = ForgeFileReadService;
    type InformationRepository = ForgeKnowledgeRepository;

    fn environment_service(&self) -> &Self::EnvironmentService {
        &self._environment_service
    }

    fn file_read_service(&self) -> &Self::FileReadService {
        &self._file_read_service
    }

    fn information_repo(&self) -> &Self::InformationRepository {
        &self._information_repo
    }
}
