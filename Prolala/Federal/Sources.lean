import Prolala.Time
import Prolala.Util

open Time

inductive StateTag
| Alabama 
| Alaska 
| Arizona 
| Arkansas 
| California 
| Colorado 
| Connecticut 
| Delaware 
| Florida 
| Georgia 
| Hawaii 
| Idaho 
| Illinois 
| Indiana 
| Iowa 
| Kansas 
| Kentucky 
| Louisiana 
| Maine 
| Maryland 
| Massachusetts 
| Michigan 
| Minnesota 
| Mississippi 
| Missouri 
| Montana 
| Nebraska 
| Nevada 
| New 
| Hampshire 
| NewJersey 
| NewMexico 
| NewYork 
| NorthCarolina 
| NorthDakota 
| Ohio 
| Oklahoma 
| Oregon 
| Pennsylvania 
| Rhode 
| Island 
| SouthCarolina 
| SouthDakota 
| Tennessee 
| Texas 
| Utah 
| Vermont 
| Virginia 
| Washington 
| WestVirginia 
| WisconsinWyoming
| WashingtonDC
| AmericanSamoa 
| Guam 
| NorthernMarianaIslands 
| PuertoRico 
| USVirginIslands
deriving DecidableEq, Repr

instance : ToString StateTag where
  toString := reprStr

class HasPriority (A : Type u) where
  priority : A → Nat


inductive Court where
| supreme
| firstCircuit
| secondCircuit
| thirdCircuit
| fourthCircuit
| fifthCircuit
| sixthCircuit
| seventhCircuit
| eighthCircuit
| ninthCircuit
| tenthCircuit
| eleventhCircuit
| dcCircuit
| federalCircuit
--
| districtOfColumbia
| districtOfMaine
| districtOfMassachusetts
| districtOfNewHampshire
| districtOfPuertoRico
| districtOfRhodeIsland
--Second Circuit (New York City)
| districtOfConnecticut
| easternDistrictOfNewYork
| northernDistrictOfNewYork
| southernDistrictOfNewYork
| westernDistrictOfNewYork
| districtOfVermont

--Third Circuit (Philadelphia)
| districtOfDelaware
| districtOfNewJersey
| easternDistrictOfPennsylvania
| middleDistrictOfPennsylvania
| westernDistrictOfPennsylvania
| districtOfTheVirginIslands

--Fourth Circuit (Richmond)
| districtOfMaryland
| easternDistrictOfNorthCarolina
| middleDistrictOfNorthCarolina
| westernDistrictOfNorthCarolina
| districtOfSouthCarolina
| easternDistrictOfVirginia
| westernDistrictOfVirginia
| northernDistrictOfWestVirginia
| southernDistrictOfWestVirginia

--Fifth Circuit (New Orleans)
| easternDistrictOfLouisiana
| middleDistrictOfLouisiana
| westernDistrictOfLouisiana
| northernDistrictOfMississippi
| southernDistrictOfMississippi
| easternDistrictOfTexas
| northernDistrictOfTexas
| wouthernDistrictOfTexas
| westernDistrictofTexas

--Sixth Circuit (Cincinnati)
| easternDistrictOfKentucky
| westernDistrictOfKentucky
| easternDistrictOfMichigan
| westernDistrictOfMichigan
| northernDistrictOfOhio
| southernDistrictOfOhio
| easternDistrictOfTennessee
| middleDistrictOfTennessee
| westernDistrictOfTennessee

--Seventh Circuit (Chicago)
| centralDistrictOfIllinois
| northernDistrictOfIllinois
| southernDistrictOfIllinois
| northernDistrictOfIndiana
| southernDistrictOfIndiana
| easternDistrictOfWisconsin
| westernDistrictOfWisconsin

--Eighth Circuit (St. Louis)
| easternDistrictOfArkansas
| westernDistrictOfArkansas
| northernDistrictOfIowa
| southernDistrictOfIowa
| districtOfMinnesota
| easternDistrictOfMissouri
| westernDistrictOfMissouri
| districtOfNebraska
| districtOfNorthDakota
| districtOfSouthDakota

--Ninth Circuit (San Francisco)
| districtOfAlaska
| districtOfArizona
| centralDistrictOfCalifornia
| easternDistrictOfCalifornia
| northernDistrictOfCalifornia
| southernDistrictOfCalifornia
| districtOfGuam
| districtOfHawaii
| districtOfIdaho
| districtOfMontana
| districtOfNevada
| districtOfTheNorthernMarianaIslands
| districtOfOregon
| easternDistrictOfWashington
| westernDistrictOfWashington

--Tenth Circuit (Denver)
| districtOfColorado
| districtOfKansas
| districtOfNewMexico
| easternDistrictOfOklahoma
| northernDistrictOfOklahoma
| westernDistrictOfOklahoma
| districtOfUtah
| districtOfWyoming

--Eleventh Circuit (Atlanta)
| middleDistrictOfAlabama
| northernDistrictOfAlabama
| southernDistrictOfAlabama
| middleDistrictOfFlorida
| northernDistrictOfFlorida
| southernDistrictOfFlorida
| middleDistrictOfGeorgia
| northernDistrictOfGeorgia
| southernDistrictOfGeorgia
--
| civilianBoardOfContractAppeals
| unitedStatesTaxCourt
| patentTrialAndAppealBoard
| internationalTradeCommission
| unitedStatesCourtOfInternationalTrade
| unitedStatesCourtOfFederalClaims
| unitedStatesForeignIntelligenceSurveillanceCourt
| unitedStatesBankruptcyCourts
| trademarkTrialAndAppealBoard
| unitedStatesMeritSystemsProtectionBoard
| unitedStatesAlienTerroristRemovalCourt
| armedServicesBoardOfContractAppeals
| officeOfCompliance
| personnelAppealsBoard
--
| courtOfAppealsForVeteransClaims
| boardOfVeteransAppeals
| courtOfAppealsForTheArmedForces
| unitedStatesArmyCourtOfCriminalAppeals
| navyMarineCorpsCourtOfCriminalAppeals
| airForceCourtOfCriminalAppeals
| coastGuardCourtOfCriminalAppeals
| boardOfImmigrationAppeals
| unitedStatesForeignIntelligenceSurveillanceCourtOfReview
| unitedStatesCourtOfMilitaryCommissionReview
| postalServiceBoardOfContractAppeals
| officeOfDisputeResolutionForAcquisition
deriving DecidableEq, Repr

instance : ToString Court where
  toString d := (unCamelCase $ endOnly <| reprStr d).map Char.toUpper

def Court.circuitCourts : List Court := [
  firstCircuit,
  secondCircuit,
  thirdCircuit,
  fourthCircuit,
  fifthCircuit,
  sixthCircuit,
  seventhCircuit,
  eighthCircuit,
  ninthCircuit,
  tenthCircuit,
  eleventhCircuit,
  dcCircuit,
  federalCircuit
]

def Court.districtCourts : List Court := [
  districtOfColumbia,
  districtOfMaine,
  districtOfMassachusetts,
  districtOfNewHampshire,
  districtOfPuertoRico,
  districtOfRhodeIsland,
  districtOfConnecticut,
  easternDistrictOfNewYork,
  northernDistrictOfNewYork,
  southernDistrictOfNewYork,
  westernDistrictOfNewYork,
  districtOfVermont,
  districtOfDelaware,
  districtOfNewJersey,
  easternDistrictOfPennsylvania,
  middleDistrictOfPennsylvania,
  westernDistrictOfPennsylvania,
  districtOfTheVirginIslands,
  districtOfMaryland,
  easternDistrictOfNorthCarolina,
  middleDistrictOfNorthCarolina,
  westernDistrictOfNorthCarolina,
  districtOfSouthCarolina,
  easternDistrictOfVirginia,
  westernDistrictOfVirginia,
  northernDistrictOfWestVirginia,
  southernDistrictOfWestVirginia,
  easternDistrictOfLouisiana,
  middleDistrictOfLouisiana,
  westernDistrictOfLouisiana,
  northernDistrictOfMississippi,
  southernDistrictOfMississippi,
  easternDistrictOfTexas,
  northernDistrictOfTexas,
  wouthernDistrictOfTexas,
  westernDistrictofTexas,
  easternDistrictOfKentucky,
  westernDistrictOfKentucky,
  easternDistrictOfMichigan,
  westernDistrictOfMichigan,
  northernDistrictOfOhio,
  southernDistrictOfOhio,
  easternDistrictOfTennessee,
  middleDistrictOfTennessee,
  westernDistrictOfTennessee,
  centralDistrictOfIllinois,
  northernDistrictOfIllinois,
  southernDistrictOfIllinois,
  northernDistrictOfIndiana,
  southernDistrictOfIndiana,
  easternDistrictOfWisconsin,
  westernDistrictOfWisconsin,
  easternDistrictOfArkansas,
  westernDistrictOfArkansas,
  northernDistrictOfIowa,
  southernDistrictOfIowa,
  districtOfMinnesota,
  easternDistrictOfMissouri,
  westernDistrictOfMissouri,
  districtOfNebraska,
  districtOfNorthDakota,
  districtOfSouthDakota,
  districtOfAlaska,
  districtOfArizona,
  centralDistrictOfCalifornia,
  easternDistrictOfCalifornia,
  northernDistrictOfCalifornia,
  southernDistrictOfCalifornia,
  districtOfGuam,
  districtOfHawaii,
  districtOfIdaho,
  districtOfMontana,
  districtOfNevada,
  districtOfTheNorthernMarianaIslands,
  districtOfOregon,
  easternDistrictOfWashington,
  westernDistrictOfWashington,
  districtOfColorado,
  districtOfKansas,
  districtOfNewMexico,
  easternDistrictOfOklahoma,
  northernDistrictOfOklahoma,
  westernDistrictOfOklahoma,
  districtOfUtah,
  districtOfWyoming,
  middleDistrictOfAlabama,
  northernDistrictOfAlabama,
  southernDistrictOfAlabama,
  middleDistrictOfFlorida,
  northernDistrictOfFlorida,
  southernDistrictOfFlorida,
  middleDistrictOfGeorgia,
  northernDistrictOfGeorgia,
  southernDistrictOfGeorgia
]

abbrev Court.CircuitCourt := { c : Court // c ∈ circuitCourts }
abbrev Court.DistrictCourt := { c : Court // c ∈ districtCourts }

def Court.priority : Court → Nat
| supreme => 1
| firstCircuit => 2
| secondCircuit => 2
| thirdCircuit => 2
| fourthCircuit => 2
| fifthCircuit => 2
| sixthCircuit => 2
| seventhCircuit => 2
| eighthCircuit => 2
| ninthCircuit => 2
| tenthCircuit => 2
| eleventhCircuit => 2
| dcCircuit => 2
| federalCircuit => 2
| districtOfColumbia => 3
| districtOfMaine => 3
| districtOfMassachusetts => 3
| districtOfNewHampshire => 3
| districtOfPuertoRico => 3
| districtOfRhodeIsland => 3
| districtOfConnecticut => 3
| easternDistrictOfNewYork => 3
| northernDistrictOfNewYork => 3
| southernDistrictOfNewYork => 3
| westernDistrictOfNewYork => 3
| districtOfVermont => 3
| districtOfDelaware => 3
| districtOfNewJersey => 3
| easternDistrictOfPennsylvania => 3
| middleDistrictOfPennsylvania => 3
| westernDistrictOfPennsylvania => 3
| districtOfTheVirginIslands => 3
| districtOfMaryland => 3
| easternDistrictOfNorthCarolina => 3
| middleDistrictOfNorthCarolina => 3
| westernDistrictOfNorthCarolina => 3
| districtOfSouthCarolina => 3
| easternDistrictOfVirginia => 3
| westernDistrictOfVirginia => 3
| northernDistrictOfWestVirginia => 3
| southernDistrictOfWestVirginia => 3
| easternDistrictOfLouisiana => 3
| middleDistrictOfLouisiana => 3
| westernDistrictOfLouisiana => 3
| northernDistrictOfMississippi => 3
| southernDistrictOfMississippi => 3
| easternDistrictOfTexas => 3
| northernDistrictOfTexas => 3
| wouthernDistrictOfTexas => 3
| westernDistrictofTexas => 3
| easternDistrictOfKentucky => 3
| westernDistrictOfKentucky => 3
| easternDistrictOfMichigan => 3
| westernDistrictOfMichigan => 3
| northernDistrictOfOhio => 3
| southernDistrictOfOhio => 3
| easternDistrictOfTennessee => 3
| middleDistrictOfTennessee => 3
| westernDistrictOfTennessee => 3
| centralDistrictOfIllinois => 3
| northernDistrictOfIllinois => 3
| southernDistrictOfIllinois => 3
| northernDistrictOfIndiana => 3
| southernDistrictOfIndiana => 3
| easternDistrictOfWisconsin => 3
| westernDistrictOfWisconsin => 3
| easternDistrictOfArkansas => 3
| westernDistrictOfArkansas => 3
| northernDistrictOfIowa => 3
| southernDistrictOfIowa => 3
| districtOfMinnesota => 3
| easternDistrictOfMissouri => 3
| westernDistrictOfMissouri => 3
| districtOfNebraska => 3
| districtOfNorthDakota => 3
| districtOfSouthDakota => 3
| districtOfAlaska => 3
| districtOfArizona => 3
| centralDistrictOfCalifornia => 3
| easternDistrictOfCalifornia => 3
| northernDistrictOfCalifornia => 3
| southernDistrictOfCalifornia => 3
| districtOfGuam => 3
| districtOfHawaii => 3
| districtOfIdaho => 3
| districtOfMontana => 3
| districtOfNevada => 3
| districtOfTheNorthernMarianaIslands => 3
| districtOfOregon => 3
| easternDistrictOfWashington => 3
| westernDistrictOfWashington => 3
| districtOfColorado => 3
| districtOfKansas => 3
| districtOfNewMexico => 3
| easternDistrictOfOklahoma => 3
| northernDistrictOfOklahoma => 3
| westernDistrictOfOklahoma => 3
| districtOfUtah => 3
| districtOfWyoming => 3
| middleDistrictOfAlabama => 3
| northernDistrictOfAlabama => 3
| southernDistrictOfAlabama => 3
| middleDistrictOfFlorida => 3
| northernDistrictOfFlorida => 3
| southernDistrictOfFlorida => 3
| middleDistrictOfGeorgia => 3
| northernDistrictOfGeorgia => 3
| southernDistrictOfGeorgia => 3
/- sjm original jurisdiction -/
| civilianBoardOfContractAppeals => 3
| unitedStatesTaxCourt => 3
| patentTrialAndAppealBoard => 3
| internationalTradeCommission => 3
| unitedStatesCourtOfInternationalTrade => 3
| unitedStatesCourtOfFederalClaims => 3
| unitedStatesForeignIntelligenceSurveillanceCourt => 3
| unitedStatesBankruptcyCourts => 3
| trademarkTrialAndAppealBoard => 3
| unitedStatesMeritSystemsProtectionBoard => 3
| unitedStatesAlienTerroristRemovalCourt => 3
| armedServicesBoardOfContractAppeals => 3
| officeOfCompliance => 3
| personnelAppealsBoard => 3
/- sjm appellate -/
| courtOfAppealsForVeteransClaims => 2
| courtOfAppealsForTheArmedForces => 2
| unitedStatesArmyCourtOfCriminalAppeals => 2
| navyMarineCorpsCourtOfCriminalAppeals => 2
| airForceCourtOfCriminalAppeals => 2
| coastGuardCourtOfCriminalAppeals => 2
| boardOfImmigrationAppeals => 2
| unitedStatesForeignIntelligenceSurveillanceCourtOfReview => 2
| unitedStatesCourtOfMilitaryCommissionReview => 2
| postalServiceBoardOfContractAppeals => 2
| officeOfDisputeResolutionForAcquisition => 2
/- These guys appeal to the CoA for veterans claims, who appeal to the Federal Circuit. -/
| boardOfVeteransAppeals => 3


inductive Legislative
| usc (title : Nat) : Legislative
| treaty : Legislative
deriving DecidableEq, Repr

def Legislative.priority : Legislative → Nat
| usc _ => 1
| treaty => 1

inductive Executive
| order : Executive
deriving DecidableEq, Repr

def Executive.priority : Executive → Nat
| order => 1

inductive AdministrativeBody
| irs
deriving DecidableEq, Repr

inductive Administrative
| cfr (title : Nat) : Administrative
| ruling (issuedBy : AdministrativeBody) : Administrative
| miscGuidance (issuedBy : AdministrativeBody) : Administrative
deriving DecidableEq, Repr

def Administrative.priority : Administrative → Nat
| cfr _ => 2
| ruling _ => 4
| miscGuidance _ => 5

inductive SourceOfLaw
| constitution : SourceOfLaw
| legislative : Legislative → SourceOfLaw
| executive : Executive → SourceOfLaw
| court : Court → SourceOfLaw
| administrative : Administrative → SourceOfLaw
deriving Repr, DecidableEq

def SourceOfLaw.priority : SourceOfLaw → Nat
| constitution => 0
| legislative s => s.priority
| executive s => s.priority
| court s => s.priority
| administrative s => s.priority

instance : LE SourceOfLaw where
  le := InvImage Nat.le SourceOfLaw.priority

instance : LT SourceOfLaw where
  lt := InvImage Nat.lt SourceOfLaw.priority

instance (s₁ s₂ : SourceOfLaw) : Decidable <| s₁ <= s₂ := inferInstanceAs <| Decidable <| s₁.priority <= s₂.priority
instance (s₁ s₂ : SourceOfLaw) : Decidable <| s₁ < s₂ := inferInstanceAs <| Decidable <| s₁.priority < s₂.priority

instance : Coe Legislative SourceOfLaw where
  coe := SourceOfLaw.legislative

instance : Coe Executive SourceOfLaw where
  coe := SourceOfLaw.executive

instance : Coe Court SourceOfLaw where
  coe := SourceOfLaw.court

instance : Coe Administrative SourceOfLaw where
  coe := SourceOfLaw.administrative

