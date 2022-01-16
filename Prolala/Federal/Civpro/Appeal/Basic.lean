import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Appeal.Defs
import Prolala.Federal.Civpro.Defs

open Time
inductive Appeal.Step where
deriving DecidableEq, Repr

inductive Appeal.WfStep : Civpro.State -> Step -> Civpro.State -> Prop
