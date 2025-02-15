use std::sync::Arc;

use forge_domain::App;

use crate::provider::ForgeProviderService;
use crate::tool_service::ForgeToolService;
use crate::Infrastructure;

pub struct ForgeApp<F> {
    infra: Arc<F>,
    _tool_service: ForgeToolService,
    _provider_service: ForgeProviderService,
}

impl<F: Infrastructure> ForgeApp<F> {
    pub fn new(infra: Arc<F>) -> Self {
        Self {
            infra: infra.clone(),
            _tool_service: ForgeToolService::new(infra.clone()),
            _provider_service: ForgeProviderService::new(infra.clone()),
        }
    }
}

impl<F: Infrastructure> App for ForgeApp<F> {
    type ToolService = ForgeToolService;
    type ProviderService = ForgeProviderService;
    type ConversationRepository = F::ConversationRepository;

    fn tool_service(&self) -> &Self::ToolService {
        &self._tool_service
    }

    fn provider_service(&self) -> &Self::ProviderService {
        &self._provider_service
    }

    fn conversation_repository(&self) -> &Self::ConversationRepository {
        self.infra.conversation_repository()
    }
}

impl<F: Infrastructure> Infrastructure for ForgeApp<F> {
    type EnvironmentService = F::EnvironmentService;
    type ConversationRepository = F::ConversationRepository;
    type FileReadService = F::FileReadService;

    fn environment_service(&self) -> &Self::EnvironmentService {
        self.infra.environment_service()
    }

    fn file_read_service(&self) -> &Self::FileReadService {
        self.infra.file_read_service()
    }

    fn conversation_repository(&self) -> &Self::ConversationRepository {
        self.infra.conversation_repository()
    }
}
