use proc_macro2::Span;
use syn::{punctuated::Punctuated, Generics};

// TODO need to only add when struct is borrowed
pub(crate) fn add_de_params(mut generics: Generics) -> Generics {
    let def = syn::LifetimeDef {
        attrs: Vec::new(),
        lifetime: syn::Lifetime::new("'de", Span::call_site()),
        colon_token: None,
        bounds: Punctuated::new(),
    };
    generics.params = Some(syn::GenericParam::Lifetime(def))
        .into_iter()
        .chain(generics.params)
        .collect();
    generics
}
