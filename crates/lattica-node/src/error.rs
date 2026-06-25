use std::fmt;

/// Reasons a shielded transaction can be rejected by the chain.
#[derive(Debug, PartialEq, Eq)]
pub enum TxError {
    BadBindingSignature,
    UnknownAnchor,
    BadMembership,
    DoubleSpend,
    BadAuthProof,
    Unbalanced { inputs: u64, outputs_plus_fee: u64 },
    TreeFull,
    Internal(&'static str),
}

impl fmt::Display for TxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TxError::BadBindingSignature => write!(f, "binding signature failed to verify"),
            TxError::UnknownAnchor => write!(f, "spend references an unknown anchor"),
            TxError::BadMembership => write!(f, "note commitment is not in the tree under the anchor"),
            TxError::DoubleSpend => write!(f, "nullifier already spent (double-spend)"),
            TxError::BadAuthProof => write!(f, "spend-authorization STARK proof failed to verify"),
            TxError::Unbalanced { inputs, outputs_plus_fee } => {
                write!(f, "value imbalance: inputs={inputs} != outputs+fee={outputs_plus_fee}")
            }
            TxError::TreeFull => write!(f, "commitment tree is full"),
            TxError::Internal(m) => write!(f, "internal error: {m}"),
        }
    }
}

impl std::error::Error for TxError {}
