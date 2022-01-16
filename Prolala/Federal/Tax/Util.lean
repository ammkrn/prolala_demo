import Prolala.Time
import Prolala.Federal.Sources

open Time

class Property (A : Type u) where
  adjustedBasis : A → Int

open Property

class PropertyTxn (A : Type u) extends Property A where
  amtRealized : A → Int
  realizedGainLoss : A → Int := fun a => amtRealized a - adjustedBasis a
  /-
  taxResult : A → PropertyTxn.TaxResult
  -/
class StandardPropertyTxn (A : Type u) extends PropertyTxn A where
  standardRealizedGainLoss (a) : realizedGainLoss a = amtRealized a - adjustedBasis a

inductive CapitalAssetKind
| collectible
| commercialRealEstate
| standard
deriving DecidableEq, Repr

class CapitalAsset (A : Type u) extends PropertyTxn A where
  originallyAcquired : A → Date
  dateOfSale : A → Date
  h_date (a) : originallyAcquired a <= dateOfSale a
  kind : A → CapitalAssetKind

inductive CapitalAssetResult
| shortTerm : Money → CapitalAssetKind → CapitalAssetResult
| longTerm : Money → CapitalAssetKind → CapitalAssetResult

def CapitalAsset.result {A : Type u} [CapitalAsset A] (a : A) : CapitalAssetResult :=
  if (dateOfSale a - originallyAcquired a) < Duration.fromYears 1 
  then CapitalAssetResult.shortTerm (PropertyTxn.realizedGainLoss a) (kind a)
  else CapitalAssetResult.longTerm (PropertyTxn.realizedGainLoss a) (kind a)

class PropertyTxn' (A : Type u) extends Property A where
  amtRealized : A → Int
  recognizedGainLoss : A → Int

class Nonrecognition (A : Type u) where
  unrecognizedGainLoss : A → Int
  recognizedGainLoss : A → Int
  deferredGainLoss : A → Int

structure Citation where
  citation : String
deriving Repr

class Conditioned (A : Type u) where
  conditions : A → List (String × Citation)

class Explain (A : Type u) where
  explain : A → String

def Tax.sourcesOfLaw : List SourceOfLaw := [
  SourceOfLaw.constitution,
  Administrative.miscGuidance AdministrativeBody.irs,
  Administrative.ruling AdministrativeBody.irs,
  Legislative.usc 26,
  Administrative.cfr 26,
  Court.supreme,
  Court.unitedStatesTaxCourt,
  Executive.order,
  Legislative.treaty
] 
++ Court.circuitCourts.map SourceOfLaw.court 
++ Court.districtCourts.map SourceOfLaw.court

abbrev Tax.SourceOfLaw := { s : _root_.SourceOfLaw // s ∈ Tax.sourcesOfLaw }

#eval qsort <| Tax.sourcesOfLaw