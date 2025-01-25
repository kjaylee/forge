use forge_domain::ForgeDomain;

use crate::{APIService, ChatService, SuggestionService, TitleService, UIService};

/// Core application trait providing access to high-level application services.
/// This trait extends ForgeDomain to provide a complete interface including both
/// domain and application layer services. It follows clean architecture principles
/// by building application services on top of domain services.
pub trait ForgeApp: ForgeDomain {
    /// The concrete type implementing API service capabilities
    type APIService: APIService;
    /// The concrete type implementing chat service capabilities
    type ChatService: ChatService;
    /// The concrete type implementing UI service capabilities
    type UIService: UIService;
    /// The concrete type implementing suggestion service capabilities
    type SuggestionService: SuggestionService;
    /// The concrete type implementing workflow title service capabilities 
    type TitleService: TitleService;

    /// Get a reference to the API service instance
    fn api_service(&self) -> &Self::APIService;
    /// Get a reference to the chat service instance
    fn chat_service(&self) -> &Self::ChatService;
    /// Get a reference to the UI service instance
    fn ui_service(&self) -> &Self::UIService;
    /// Get a reference to the suggestion service instance
    fn suggestion_service(&self) -> &Self::SuggestionService;
    /// Get a reference to the workflow title service instance
    fn title_service(&self) -> &Self::TitleService;
}