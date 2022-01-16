import Mathlib.Data.Option.Basic
import Prolala.Time
import Prolala.Util
import Prolala.Federal.Sources
import Prolala.Federal.Civpro.Pleading.Defs
import Prolala.Federal.Civpro.Pleading.Basic
import Prolala.Federal.Civpro.Defs

open Time

def ClintonJones.court : Court.DistrictCourt := ⟨Court.easternDistrictOfArkansas, by decide⟩ 
def ClintonJones.courtDivision := "Western Division"
def ClintonJones.intro := "Plaintiff Paula Corbin Jones, by counsel, brings this action to obtain redress for the deprivation and conspiracy to deprive Plaintiff of her federally protected rights as hereafter alleged, and for intentional infliction of emotional distress, and for defamation."
def ClintonJones.venue := "Venue is appropriate in this judicial district under 28 U.S.C. § 1391(b), because Defendants William Jefferson Clinton and Danny Ferguson reside here, and a substantial part of the events giving rise to this Complaint occurred here. "
def ClintonJones.jurisdiction := "This Court has subject matter jurisdiction pursuant to (a) 28 U.S.C. § 1331, because the case arises under the Constitution and laws of the United States; (b) 28 U.S.C. § 1343, because this action seeks redress and damages for violation of 42 U.S.C. § § 1983 and 1985 and, in particular, the due process and equal protection provisions of the United States Constitution, including the rights protected in the Fifth and Fourteenth Amendments thereof; and (c) 28 U.S.C. § 1232, since there is diversity of citizenship and this is a civil action involving, exclusive of interest and costs, a sum in excess of $50,000.00. This Court also has jurisdiction over the causes of action alleged in Counts III and IV pursuant to federal pendant jurisdiction."
def ClintonJones.facts := [
  "On or about March 11, 1991, Jones began work as an Arkansas State employee for the Arkansas Industrial Development Commission (hereafter \"AIDC\"), an agency within the executive branch of the State of Arkansas. The Governor of Arkansas is the chief executive officer of the executive branch of the State of Arkansas.",
  "On May 8, 1991, the AIDC sponsored the Third Annual Governor's Quality Management Conference (hereafter \"Conference\"), which was held at the Excelsior Hotel in Little Rock, Arkansas. Clinton, then Governor of Arkansas, delivered a speech at the Conference on that day.",
  "Also on that day, Jones worked at the registration desk at the Conference along with Pamela Blackard (hereafter \"Blackard\") another AIDC employee.",
  "A man approached the registration desk and informed Jones and Blackard that he was Trooper Danny Ferguson, Bill Clinton's bodyguard. Defendant Ferguson was at that time a law enforcement officer within the ranks of the Arkansas State Police and assigned to the Governor's Security Detail. He was in street clothes and displayed a firearm on his person. He made small talk with Jones and Blackard and then left.",
  "At approximately 2:30 p.m. on that day, Ferguson reappeared at the registration desk, delivered a piece of paper to Jones with a four digit number written on it and said: \"The Governor would like to meet with you\" in this suite number. Plaintiff had never met Defendant Clinton and saw him in person for the first time at the Conference.",
  "A three-way conversation followed between Ferguson, Blackard and Jones about what the Governor could want. Jones, who was then a rank-and-file Arkansas state employee being paid approximately $6.35 an hour, thought it was an honor to be asked to meet the Governor. Ferguson stated during the conversation: \"It's okay, we do this all the time for the Governor.\"",
  "Jones agreed to meet with the Governor because she thought it might lead to an enhanced employment opportunity with the State. Blackard told Jones that she would assume Plaintiff's duties at the registration desk.",
  "Trooper Ferguson then escorted Jones to the floor of the hotel suite whose number had been written on the slip of paper Trooper Ferguson had given to Jones. The door was slightly ajar when she arrived at the suite.",
  "Jones knocked on the door frame and Clinton answered. Plaintiff entered. Ferguson remained outside.",
  "The room was furnished as a business suite, not for an overnight hotel guest. It contained a couch and chairs, but no bed.",
  "Clinton shook Jones' hand, invited her in, and closed the door.",
  "A few minutes of small talk ensued, which included asking Jones about her job. Clinton told Jones that Dave Harrington is \"my good friend.\" On May 8, 1991, David Harrington was Director of the AIDC, having been appointed to that post by Governor Clinton. Harrington was Jones' ultimate superior within the AIDC.",
  "Clinton then took Jones' hand and pulled her toward him, so that their bodies were in close proximity.",
  "Jones removed her hand from his and retreated several feet.",
  "However, Clinton approached Jones again. He said: \"I love the way your hair flows down your back\" and \"I love your curves.\" While saying these things, Clinton put his hand on Plaintiff's leg and started sliding it toward the hem of Plaintiff's culottes. Clinton also bent down to attempt to kiss Jones on the neck.",
  "Jones exclaimed, \"What are you doing?\" and escaped from Clinton's physical proximity by walking away from him. Jones tried to distract Clinton by chatting with him about his wife. Jones later took a seat at the end of the sofa nearest the door. Clinton asked Jones: \"Are you married?\" She responded that she had a regular boyfriend. Clinton then approached the sofa and as he sat down he lowered his trousers and underwear exposing his erect penis and asked Jones to \"kiss it.\"",
  "There were distinguishing characteristics in Clinton's genital area that were obvious to Jones.",
  "Jones became horrified, jumped up from the couch, stated that she was \"not that kind of girl\" and said: \"Look, I've got to go.\" She attempted to explain that she would get in trouble for being away from the registration desk.",
  "Clinton, while fondling his penis said: \"Well, I don't want to make you do anything you don't want to do.\" Clinton then stood up and pulled up his pants and said: \"If you get in trouble for leaving work, have Dave call me immediately and I'll take care of it.\" As Jones left the room Clinton looked sternly at Jones and said: \"You are smart. Let's keep this between ourselves.\"",
  "Jones believed \"Dave\" to be the same David Harrington, of whom Clinton previously referred. Clinton, by his comments about Harrington to Jones, affirmed that he had control over Jones' employment, and that he was willing to use that power. Jones became fearful that her refusal to succumb to Clinton's advances could damage her in her job and even jeopardize her employment.",
  "At no time, nor in any manner, did Jones encourage Clinton to turn the meeting toward a sexual liaison. To the contrary, the unwanted sexual advances made by Clinton were repugnant and abhorrent to Jones who took all reasonable steps she could think to do to terminate Clinton's perverse attention and actions toward her.",
  "Jones left the hotel suite and came into the presence of Trooper Ferguson in the hallway. Ferguson did not escort Plaintiff back to the registration desk. Jones said nothing to Ferguson and he said nothing to her during her departure from the suite.",
  "Jones was visibly shaken and upset when she returned to the registration desk. Pamela Blackard immediately asked her what was wrong. After a moment, during which Jones attempted to collect herself, she told Blackard much of what had happened. Blackard attempted to comfort Plaintiff.",
  "Jones thereafter left the Conference and went to the work place of her friend, Debra Ballentine.",
  "When Ballentine met Plaintiff at the reception area, she immediately asked Jones what was wrong because Jones was visibly upset and nervous. Plaintiff wanted to talk about something that just happened and wanted to discuss it someplace privately. Ballentine and Jones went to a private area in the office, and later outside. Jones then told Ballentine what had happened with Clinton in the hotel suite. According to Ballentine, Jones told her that Clinton said as she left the room, \"I know you're a smart girl and I'm sure you'll keep this to yourself.\"",
  "Ballentine urged Jones to report the incident. Plaintiff refused, fearing that, if she did so, no one would believe her account, that she would lose her job, and that the incident would endanger her relationship with her then-fiance (now husband), Stephen Jones.",
  "Later, on the same day, Plaintiff also described the substance of her encounter with Clinton to her sister, Charlotte Corbin Brown.",
  "Within two days of May 8, 1991, Plaintiff also informed her sister, Lydia Corbin Cathey, and her mother, Delmar Lee Corbin, the substance of her encounter with Clinton.",
  "Plaintiff also told her fiance, Stephen Jones, that \"Bill Clinton made a pass at me but I said 'no'.\" She, however, did not at that time tell him the lurid details of her horrific encounter with Clinton in the hotel suite, which she feared, if disclosed, might ruin her relationship with Mr. Jones.",
  "Plaintiff continued to work at AIDC. One of her duties was to deliver documents to and from the Office of the Governor, as well as other offices within the Arkansas State Capitol complex. In or about June, 1991, while Jones was performing this duty, Ferguson saw her at the Governor's office and said: \"Bill wants your phone number. Hillary's out of town often and Bill would like to see you.\" Plaintiff refused to provide her telephone number.",
  "On another occasion, Ferguson approached Jones and asked: \"How's Steve?\" This frightened Plaintiff and made her feel as if she was being watched and was not safe. She had never told Ferguson or Clinton the name of her fiance.",
  "Plaintiff and Stephen Jones later married. She gave birth to her child and returned to work, after which she encountered Ferguson at Governor Clinton's office. Ferguson told her: \"I've told Bill how good looking you are since you've had the baby.\" This, too, frightened Plaintiff and made her feel that her activities were being monitored.",
  "On one occasion, Plaintiff was accosted by Clinton in the Rotunda of the Arkansas State Capitol. Clinton draped his arm over Plaintiff, pulled her close and tightly to his body and said: \"Don't we make a beautiful couple – beauty and the beast?\" Clinton directed this remark to his bodyguard, Trooper Larry Patterson, an officer of the Arkansas State Police and also a member of the Governor's Security Detail.",
  "Jones continued to work at AIDC even though she was in constant fear that Governor Clinton might take retaliatory action against her because of her rejection of his abhorrent sexual advances. Her enjoyment of her work was severely diminished. In fact, she was treated in a hostile and rude manner by certain superiors in AIDC. This rude conduct had not happened prior to her encounter with Clinton. Further, after her maternity leave she was transferred to a position which had no responsible duties for which she could be adequately evaluated to earn advancement. The reason given to her by her superiors for the transfer was that her previous position had been eliminated. This reason was untrue since her former position was not abolished. It was a pretext for the real reason which was that she was being punished for her rejection of the various advances made by Clinton described above. In addition, the job in which she was placed called for a higher grade and pay, yet she was not paid more money than she received in her previous position. Although other employees received merit increases, Jones never received a raise beyond a cost of living increase.",
  "Jones terminated her employment and separated from AIDC service on February 20, 1993. On May 4, 1993, Plaintiff, her husband and child moved to California.",
  "In January, 1994, Plaintiff visited her family and friends in Arkansas. While Jones was in Arkansas, Ms. Ballentine telephoned Jones to arrange a meeting for lunch. During the telephone conversation, Ballentine read to Plaintiff a paragraph from an article published in the January, 1994 issue of The American Spectator magazine regarding Plaintiff's hotel suite encounter with Clinton. Attached hereto, and incorporated herein, as Exhibit \"A\" is a copy of The American Spectator article.",
  "The American Spectator account asserts that a woman by the name of \"Paula\" told an unnamed trooper (obviously Defendant Ferguson), who had escorted \"Paula\" to Clinton's hotel room, that \"she was available to be Clinton's regular girlfriend if he so desired,\" thus implying a consummated and satisfying sexual encounter with Clinton, as well as a willingness to continue a sexual relationship with him. These assertions are untrue. The article, using information apparently derived from Ferguson, also incorrectly asserts that the encounter took place in the evening.",
  "The American Spectator account also asserted that the troopers' \"'official' duties included facilitating Clinton's cheating on his wife. This meant that, on the State payroll, and using State time, vehicles and resources, they were instructed by Clinton on a regular basis to approach women and to solicit their telephone numbers for the Governor, to drive him in State vehicles to rendezvous points and guard him during sexual encounters; to secure hotel rooms and other meeting places for sex; . . .\" and various other things to facilitate Clinton's sex life including \"to help Clinton cover-up his activities by keeping tabs on Hillary's whereabouts and lying to Hillary about her husband's whereabouts.\" Although this pattern of conduct by Clinton may be true, the magazine article concluded, evidently from interviews with troopers from Clinton's Security Detail, including Ferguson, that \"all of the women appear to have been willing participants in the affairs and liaisons [emphasis added].\"",
  "Since Jones (\"Paula\") was one of the women preyed upon by Clinton and his troopers, including by Defendant Ferguson, in the manner described above, those who read this magazine account could conclude falsely that Jones (\"Paula\") had a sexual relationship and affair with Clinton. Jones' reputation within her community was thus seriously damaged.",
  "Jones realized that those persons who already knew about the hotel room encounter could identify her as the \"Paula\" mentioned in The American Spectator article. She became extremely upset because, inter alia, she feared that the statements in the magazine would damage her relationship with her husband, her family, and her friends and acquaintances, some of whom might have believed that she had agreed to be Clinton's \"girlfriend\" at a time when she was engaged to Mr. Jones.",
  "On January 8, 1994, at approximately 12:00 noon, Jones and Ballentine were dining at the Golden Corral Steakhouse in North Little Rock, Arkansas. Trooper Ferguson, who happened to be dining with his wife at this restaurant, came over to their table to talk to Jones. Since Jones believed that the ultimate source of the report in The American Spectator of the hotel suite encounter was Trooper Ferguson, she confronted him on this matter. Trooper Ferguson stated that he was sorry that Jones' first name had appeared in the magazine article but that he had purposely concealed her last name and place of employment from those to whom he recounted the incident. Trooper Ferguson also said that he knew Jones had rebuffed Mr. Clinton's sexual advances because, \"Clinton told me you wouldn't do anything anyway, Paula.\"",
  "Because the false statements appearing in The American Spectator article that Jones was willing to have sex with Clinton (and the innuendo that she had already done so when she left the hotel suite) threatened her marriage, her friendships, and her family relationships, Plaintiff spoke publicly on February 11, 1994, that she was the \"Paula\" mentioned in The American Spectator article, that she had rebuffed Clinton's sexual advances, and that she had not expressed a willingness to be his girlfriend. Jones and her lawyer asked that Clinton acknowledge the incident, state that Jones had rejected Clinton's advances, and apologize to Jones.",
  "Clinton, who is now President of the United States of America responded to Jones' request for an apology by having his press spokespersons deliver a statement on his behalf that the incident never happened, and that he never met Plaintiff. Thus, by innuendo and effect, Clinton publicly branded Plaintiff a liar. Moreover, as recently as the week this Complaint was filed, Clinton, through his White House aides, stated that Plaintiff's account of the hotel room incident was untrue and a \"cheap political trick.\"",
  "Clinton hired an attorney, who, as Clinton's agent, said that Jones' account \"is really just another effort to rewrite the results of the election [i.e. for President of the United States] and . . . distract the President from his agenda.\" The attorney further asked the question: \"Why are these claims being brought now, three years after the fact?\" The attorney also asked how Jones' allegations could be taken \"seriously.\" These comments by Clinton's counsel, on behalf of Clinton, imply that Jones is a liar",
  "Dee Dee Meyers, White House Spokeswoman, said of Jones' allegations: \"It's just not true.\" Thus, the pattern of defaming Jones continues to this date.",
  "Clinton knows that Jones' allegations are true and that his, and his attorney's, spokespersons', and agents' denials are false.",
  "The outrageous nature of Clinton's branding of Jones as a liar is aggravated in that a greater stigma and reputation loss is suffered by Jones by the statements of the President of the United States in whom the general public reposes trust and confidence in the integrity of the holder of that office.",
  "Clinton, a member of the Arkansas State Bar, knew or should have known on May 8, 1991, and thereafter, that Arkansas law provides that harassment, including the touching or attempt or threat to do so which subjects the victim to offensive or potentially offensive physical contact, is a criminal violation of Arkansas Code Annotated 5-71-208.",
  "While Jones was in Clinton's hotel suite, Jones was falsely imprisoned by Clinton's intentional restriction of her personal freedom of movement without legal right. Clinton's use of force in pulling Jones toward him, his words and acts, and the armed police guard outside the door, in conjunction with the impressive atmosphere of her being alone with the Governor of the State who was also her superior's boss, caused her to be initially and temporarily afraid to terminate the meeting.",
  "The statements, acts, and omissions of Clinton's agents, servants, and employees who acted under his explicit and implicit instructions and supervision, during the pertinent periods herein when he was Governor of Arkansas, and after he became President, bind Clinton under the doctrines of agency, joint conduct, master-servant, respondeat superior, and conspiracy.",
  "The actions of the Arkansas state employees, including Defendant Ferguson and other agents of Clinton were taken under color of state law.",
  "Clinton's actions and omissions above stated caused Jones embarrassment, humiliation, fear, emotional distress, horror, grief, shame, marital discord and loss of reputation."
]

def ClintonJones.count1 : Count := {
  causeOfAction := "DEPRIVATION OF CONSTITUTIONAL RIGHTS AND PRIVILEGES (42 U.S.C. § 1983)",
  explanation := [
    "Plaintiff incorporates by reference paragraphs 1 through 57.",
    "Plaintiff is entitled to the equal protection of the laws under the Fourteenth Amendment of the United States Constitution, and due process of law under the Fifth and Fourteenth Amendments of the United States Constitution.",
    "Defendant Clinton, as Governor of Arkansas, acting under color of state law, discriminated against Plaintiff because of her gender by sexually harassing and assaulting her on May 8, 1991, and thereafter, and this deprived Jones of her right to equal protection of the law.",
    "Further, he continued personally, and through agents, to impose a hostile work environment on Plaintiff in which she feared the loss of her employment and the possible adverse employment actions against her, including job discrimination and monitoring of her personal life. As described above she was placed in a category separate from other public employees in that she was actually subjected to hostility by her superiors, which deprived her of an opportunity for advancement and she suffered an economic depravation.",
    "Plaintiff, as a citizen and Arkansas state employee, was entitled to due process protection of freedom from arbitrary action which jeopardized her property interest in her public employee job in that she should not have been subjected arbitrarily to the fear of losing that job or of having to provide sex to the Governor as a quid pro quo for keeping the job. Further, she should not have been subjected arbitrarily to the fear of losing the enjoyment of a proper and pleasant work environment, or to other adverse actions which she feared and which deprived her of the proper enjoyment and efficiency of her work. Clinton's actions deprived Jones of her due process liberty and property interests guaranteed to her by the Constitution of the United States.",
    "Plaintiff also was entitled to a due process liberty interest in her reputation as an honest public employee. Clinton's actions and statements deprived Jones of these rights.",
    "Plaintiff, for a brief period of time, was held against her will by the oppressive atmosphere of intimidation caused by the presence of the highest official of the State of Arkansas and an armed guard at the door. Not only was she subjected to unwelcome sexual advances, but also was personally restrained and imprisoned by the seizing of her person, against her will, by Clinton and his agent.",
    "The above-described actions of Clinton were undertaken when he was acting under the color of state law, as Governor of Arkansas, and said actions deprived Jones of federal equal protection and due process rights guaranteed by the Fifth and Fourteenth Amendments of the United States Constitution, and made actionable by 42 U.S.C. § 1983 (The Civil Rights Act). "
  ]
}

def ClintonJones.count2 : Count := {
  causeOfAction := "CONSPIRACY TO DEPRIVING PERSONS OF EQUAL PROTECTION OF THE LAWS (42 U.S.C. § 1985)",
  explanation := [
    "Plaintiff incorporates by reference paragraphs 1 through 65.",
    "Clinton conspired with his Security Detail, including with Defendant Ferguson, and perhaps with others currently unknown to this Plaintiff, to deprive Jones of equal protection of the laws and of equal privileges and immunities under the laws, as further set forth in Count I above.",
    "The conspirators committed some acts in furtherance of the conspiracy which included contacting Jones and bringing her to Clinton on May 8, 1991 to permit him to attempt to entice her on to have a sexual liaison with him.",
    "As a result of the conspiracy, Jones was injured by Defendants in her person and property and deprived of having and exercising her rights and privileges as a citizen of the United States, as is more fully set forth in Count I. "
  ]
}

def ClintonJones.count3 : Count := {
  causeOfAction := "INTENTIONAL INFLICTION OF EMOTIONAL DISTRESS"
  explanation := [
    "Plaintiff incorporates by reference paragraphs 1 through 69.",
    "The conduct of Clinton herein set forth was odious, perverse and outrageous. Not only were the acts of sexual perversity unwelcome by Jones, but they were wilful, wanton, reckless, intentional, persistent and continuous in the hotel room.",
    "Clinton's sexual advances, assaults upon and imprisonment of Jones' person, and his exposure of his erect penis and his requests of acts to be performed thereupon were extreme, intentional, and caused Jones severe emotional distress.",
    "Not content with the events in the hotel on May 8, 1991, Clinton on subsequent occasions, acting himself and through his agents, as specified above, aggravated further the initial severe emotional damage to Jones.",
    "These actions were so outrageous in character, and extreme in degree, as to go beyond all possible bounds of decency, and to be regarded as atrocious and utterly intolerable in a civilized society. "
  ]
}

def ClintonJones.count4 : Count := {
  causeOfAction := "DEFAMATION"
  explanation := [
    "Plaintiff incorporates by reference paragraphs 1 through 74.",
    "On several occasions on and after February 11, 1994, Clinton, and his agents and employees acting pursuant to his direction, maliciously and wilfully, defamed Jones by making statements which Clinton knew to be false. These statements were made with the intent and certain knowledge that they would be reprinted in the print and other media.",
    "Such statements by Clinton, his agents and employees, characterized Jones as a liar and as being \"pathetic,\" and damaged her good name, character, and reputation.",
    "Defendant Ferguson's statements likewise maliciously and willfully defamed plaintiff and damaged her good name, character and reputation. Ferguson's statement that Jones had agreed to be Clinton's girlfriend, and his innuendo that she had willingly participated in a sexual encounter, were knowingly false.",
    "That Ferguson knew these statements were false is confirmed by Clinton's denial to Ferguson that anything happened of a sexual nature between Clinton and Jones. "
  ]
}

def ClintonJones.prayerForRelief := [
  "judgment against Defendant Clinton for compensatory damages of $75,000.00; punitive damages for Defendant's wilful, outrageous and malicious conduct, of $100,000.00; the costs of her suit and attorneys' fees; nominal damages, and such other and further relief as the Court may deem proper.",
  "judgment against Defendant Clinton and Defendant Ferguson, jointly and severally for compensatory damages of $75,000.00; punitive damages for Defendant's wilful, outrageous and malicious conduct, of $100,000.00; the costs of her suit and attorney's fees; nominal damages, and such other and further relief as the Court may deem proper.",
  "judgment against Defendant Clinton for compensatory damages of $75,000.00; punitive damages for Defendant's wilful, outrageous and malicious statements and conduct, of $100,000.00; the costs of her suit and attorneys' fees; nominal damages, and such other and further relief as the Court may deem proper.",
  "judgment against Defendant Clinton and Defendant Ferguson, jointly and severally for compensatory damages of $75,000.00; punitive damages for Defendant's wilful, outrageous and malicious statements and conduct, of $100,000.00; the costs of her suit and attorneys' fees; nominal damages, and such other and further relief as the Court may deem proper. "
]


def ClintonJones.attorneyInfo1 : AttorneyInfo := {
  name := "Gilbert K. Davis"
  qual := "VA Bar No. 4683"
  title := "Attorney for Plaintiff"
  address := "9516-C Lee Highway Fairfax, Virginia 22031"
  phone := "(703) 352-3850"
}

def ClintonJones.attorneyInfo2 : AttorneyInfo := {
  name := "Joseph Cammarata"
  qual := "VA Bar No. 35118"
  title := "Attorney for Plaintiff"
  address := "9516-C Lee Highway Fairfax, Virginia 22031"
  phone := "(703) 352-3850"
}

def ClintonJones.plaintiffs : { l : List String // ¬l.isEmpty } := ⟨["Paula Corbin Jones"], by decide⟩ 
def ClintonJones.defendants : { l : List String // ¬l.isEmpty } := ⟨["William Jefferson Clinton", "Danny Ferguson"], by decide⟩ 

def ClintonJones.complaint1 : FiledComplaint := {
  court := ⟨Court.easternDistrictOfArkansas, by decide⟩
  courtDivision := some "Western Division"
  intro := intro
  venueStatement := venue
  jurisdictionStatement := jurisdiction
  plaintiff := "Paula Corbin Jones"
  defendant := "William Jefferson Clinton"
  facts := facts
  claims := ⟨[count1, count2,count3,count4], by decide⟩
  prayerForRelief := ⟨prayerForRelief, by decide⟩ 
  requestingJuryTrial := true
  plaintiffAttorneyInfo := [attorneyInfo1, attorneyInfo2]
  filedOn := Date.fromYmd 1994 5 1
  caseNum := 9999
}

def ClintonJones.complaint2 : FiledComplaint := {
  court := ⟨Court.easternDistrictOfArkansas, by decide⟩ 
  courtDivision := some "Western Division"
  intro := intro
  venueStatement := venue
  jurisdictionStatement := jurisdiction
  plaintiff := "Paula Corbin Jones"
  defendant := "Danny Ferguson"
  facts := facts
  claims := ⟨[count1, count2,count3,count4], by decide⟩
  prayerForRelief := ⟨prayerForRelief, by decide⟩ 
  requestingJuryTrial := true
  plaintiffAttorneyInfo := [attorneyInfo1, attorneyInfo2]
  filedOn := Date.fromYmd 1994 5 1
  caseNum := 9999
}

#eval IO.println ({
  complaint := ClintonJones.complaint1
  recipientIfDifferent := none
  defInUsJudicialDistrict := true
  date := Date.fromYmd 2020 1 1
  address := "100 E. West St.\nParis, TX 75460"
  email := "qwerty@asdfhjkl.info"
  phone := "(123) 456-7890"
} : ServiceWaiverRequest)

#eval IO.println ({
  req := {
    complaint := ClintonJones.complaint1
    recipientIfDifferent := none
    defInUsJudicialDistrict := true
    date := Date.fromYmd 1994 5 1
    address := "100 E. West St.\nParis, TX 75460"
    email := "qwerty@asdfhjkl.info"
    phone := "(123) 456-7890"
  }
  date := ⟨Date.fromYmd 1994 6 1, by decide⟩
  address := "11 Bass Pro Dr.\nMemphis, TN 38105"
  email := "mmm@iddqd.gov"
  phone := "(987) 654-3210"
} : ServiceWaiverResponse)
