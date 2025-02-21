use forge_app::{EnvironmentService, Infrastructure};

use crate::env::ForgeEnvironmentService;
use crate::fs::ForgeFileService;
use crate::knowledge::QdrantKnowledgeRepository;

pub struct ForgeInfra {
    _file_read_service: ForgeFileService,
    _environment_service: ForgeEnvironmentService,
    _information_repo: QdrantKnowledgeRepository,
}

impl ForgeInfra {
    pub fn new(restricted: bool) -> Self {
        let _environment_service = ForgeEnvironmentService::new(restricted);
        let env = _environment_service.get_environment();
        Self {
            _file_read_service: ForgeFileService::new(),
            _environment_service,
            _information_repo: QdrantKnowledgeRepository::new(env, "user_feedback"),
        }
    }
}

impl Infrastructure for ForgeInfra {
    type EnvironmentService = ForgeEnvironmentService;
    type FileReadService = ForgeFileService;
    type KnowledgeRepository = QdrantKnowledgeRepository;

    fn environment_service(&self) -> &Self::EnvironmentService {
        &self._environment_service
    }

    fn file_read_service(&self) -> &Self::FileReadService {
        &self._file_read_service
    }

    fn textual_knowledge_repo(&self) -> &Self::KnowledgeRepository {
        &self._information_repo
    }
}
