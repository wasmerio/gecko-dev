/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use dom::bindings::codegen::Bindings::DOMExceptionBinding;
use dom::bindings::codegen::Bindings::DOMExceptionBinding::DOMExceptionConstants;
use dom::bindings::codegen::Bindings::DOMExceptionBinding::DOMExceptionMethods;
use dom::bindings::error::Error;
use dom::bindings::global::GlobalRef;
use dom::bindings::js::{JSRef, Temporary};
use dom::bindings::utils::{Reflector, reflect_dom_object};
use util::str::DOMString;

use std::borrow::ToOwned;

#[repr(u16)]
#[derive(Copy, Debug)]
#[jstraceable]
pub enum DOMErrorName {
    IndexSizeError = DOMExceptionConstants::INDEX_SIZE_ERR,
    HierarchyRequestError = DOMExceptionConstants::HIERARCHY_REQUEST_ERR,
    WrongDocumentError = DOMExceptionConstants::WRONG_DOCUMENT_ERR,
    InvalidCharacterError = DOMExceptionConstants::INVALID_CHARACTER_ERR,
    NoModificationAllowedError = DOMExceptionConstants::NO_MODIFICATION_ALLOWED_ERR,
    NotFoundError = DOMExceptionConstants::NOT_FOUND_ERR,
    NotSupportedError = DOMExceptionConstants::NOT_SUPPORTED_ERR,
    InvalidStateError = DOMExceptionConstants::INVALID_STATE_ERR,
    SyntaxError = DOMExceptionConstants::SYNTAX_ERR,
    InvalidModificationError = DOMExceptionConstants::INVALID_MODIFICATION_ERR,
    NamespaceError = DOMExceptionConstants::NAMESPACE_ERR,
    InvalidAccessError = DOMExceptionConstants::INVALID_ACCESS_ERR,
    SecurityError = DOMExceptionConstants::SECURITY_ERR,
    NetworkError = DOMExceptionConstants::NETWORK_ERR,
    AbortError = DOMExceptionConstants::ABORT_ERR,
    URLMismatchError = DOMExceptionConstants::URL_MISMATCH_ERR,
    QuotaExceededError = DOMExceptionConstants::QUOTA_EXCEEDED_ERR,
    TimeoutError = DOMExceptionConstants::TIMEOUT_ERR,
    InvalidNodeTypeError = DOMExceptionConstants::INVALID_NODE_TYPE_ERR,
    DataCloneError = DOMExceptionConstants::DATA_CLONE_ERR,
    EncodingError
}

impl DOMErrorName {
    fn from_error(error: Error) -> DOMErrorName {
        match error {
            Error::IndexSize => DOMErrorName::IndexSizeError,
            Error::NotFound => DOMErrorName::NotFoundError,
            Error::HierarchyRequest => DOMErrorName::HierarchyRequestError,
            Error::InvalidCharacter => DOMErrorName::InvalidCharacterError,
            Error::NotSupported => DOMErrorName::NotSupportedError,
            Error::InvalidState => DOMErrorName::InvalidStateError,
            Error::Syntax => DOMErrorName::SyntaxError,
            Error::NamespaceError => DOMErrorName::NamespaceError,
            Error::InvalidAccess => DOMErrorName::InvalidAccessError,
            Error::Security => DOMErrorName::SecurityError,
            Error::Network => DOMErrorName::NetworkError,
            Error::Abort => DOMErrorName::AbortError,
            Error::Timeout => DOMErrorName::TimeoutError,
            Error::DataClone => DOMErrorName::DataCloneError,
            Error::NoModificationAllowedError => DOMErrorName::NoModificationAllowedError,
            Error::FailureUnknown => panic!(),
        }
    }
}

#[dom_struct]
pub struct DOMException {
    reflector_: Reflector,
    code: DOMErrorName,
}

impl DOMException {
    fn new_inherited(code: DOMErrorName) -> DOMException {
        DOMException {
            reflector_: Reflector::new(),
            code: code,
        }
    }

    pub fn new(global: GlobalRef, code: DOMErrorName) -> Temporary<DOMException> {
        reflect_dom_object(box DOMException::new_inherited(code), global, DOMExceptionBinding::Wrap)
    }

    pub fn new_from_error(global: GlobalRef, code: Error) -> Temporary<DOMException> {
        DOMException::new(global, DOMErrorName::from_error(code))
    }
}

impl<'a> DOMExceptionMethods for JSRef<'a, DOMException> {
    // http://dom.spec.whatwg.org/#dom-domexception-code
    fn Code(self) -> u16 {
        match self.code {
            // http://dom.spec.whatwg.org/#concept-throw
            DOMErrorName::EncodingError => 0,
            code => code as u16
        }
    }

    // http://dom.spec.whatwg.org/#error-names-0
    fn Name(self) -> DOMString {
        format!("{:?}", self.code)
    }

    // http://dom.spec.whatwg.org/#error-names-0
    fn Message(self) -> DOMString {
        let message = match self.code {
            DOMErrorName::IndexSizeError => "The index is not in the allowed range.",
            DOMErrorName::HierarchyRequestError => "The operation would yield an incorrect node tree.",
            DOMErrorName::WrongDocumentError => "The object is in the wrong document.",
            DOMErrorName::InvalidCharacterError => "The string contains invalid characters.",
            DOMErrorName::NoModificationAllowedError => "The object can not be modified.",
            DOMErrorName::NotFoundError => "The object can not be found here.",
            DOMErrorName::NotSupportedError => "The operation is not supported.",
            DOMErrorName::InvalidStateError => "The object is in an invalid state.",
            DOMErrorName::SyntaxError => "The string did not match the expected pattern.",
            DOMErrorName::InvalidModificationError => "The object can not be modified in this way.",
            DOMErrorName::NamespaceError => "The operation is not allowed by Namespaces in XML.",
            DOMErrorName::InvalidAccessError => "The object does not support the operation or argument.",
            DOMErrorName::SecurityError => "The operation is insecure.",
            DOMErrorName::NetworkError => "A network error occurred.",
            DOMErrorName::AbortError => "The operation was aborted.",
            DOMErrorName::URLMismatchError => "The given URL does not match another URL.",
            DOMErrorName::QuotaExceededError => "The quota has been exceeded.",
            DOMErrorName::TimeoutError => "The operation timed out.",
            DOMErrorName::InvalidNodeTypeError => "The supplied node is incorrect or has an incorrect ancestor for this operation.",
            DOMErrorName::DataCloneError => "The object can not be cloned.",
            DOMErrorName::EncodingError => "The encoding operation (either encoded or decoding) failed."
        };

        message.to_owned()
    }
}
