/- AKA international shoe. -/
structure MinimumContacts where
  minimumContacts : String
  reasonableness : String
deriving DecidableEq, Repr

inductive Constitutional
| minimumContacts : MinimumContacts → Constitutional
/- AKA tag jurisdiction -/
| transient : Constitutional
| streamOfCommerce : String → Constitutional
| other : String → Constitutional
deriving DecidableEq, Repr

