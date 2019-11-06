////////////////////////////////////////////////////////////////////////////WORLD 1////////////////////////////////////////////////////////////////////////////////////

abstract sig Timeout {}
sig Running, Ended extends Timeout {} 

sig Date, Time, Position, Image, TypeOfViolation, LicensePlate {}

abstract sig ReportStatus {}
sig Pending, Confirmed extends ReportStatus {}

sig ViolationReport {
	date: one Date,
	time: one Time,
	position: one Position,
	reportImage: one Image,
	type: one TypeOfViolation,
	licensePlate: one LicensePlate,
	status: one ReportStatus
}

fact ViolationReportKey {
	all vr1: ViolationReport |
		no vr2: ViolationReport |
			vr1 != vr2 and
			vr1.licensePlate = vr2.licensePlate and
			vr1.date = vr2.date and
			vr1.time = vr2.time and
			vr1.position = vr2.position and
			vr1.type = vr2.type
}

sig ViolationReportRequest {
	violationReport: one ViolationReport,
	timeout: one Timeout
}

fact associatedToAtLeastOneViolation {
	all d: Date, t: Time, p: Position, i: Image, tov:  TypeOfViolation, lp: LicensePlate |
		some vr: ViolationReport |
			vr.date = d or
			vr.time = t or
			vr.position = p or
			vr.reportImage = i or
			vr.type = tov or
			vr.licensePlate = lp or
			vr.status = Pending or vr.status = Confirmed
}

//Every violation report is associated to one and only one violation report request.
fact ViolationReportAndRequestBijection {
	all vrr1: ViolationReportRequest |
		no vrr2: ViolationReportRequest |
			vrr1 != vrr2 and vrr1.violationReport = vrr2.violationReport
}

sig SafeStreetsApp {
	violationReportsSent: set ViolationReport,
	user: one User
}

sig User {}

// Every SafeStreets App is associated to one and only one User.
fact SafeStreetsAppUserBijection {
	all ssa1: SafeStreetsApp |
		no ssa2: SafeStreetsApp |
			ssa1 != ssa2 and ssa1.user = ssa2.user
	all u: User |
		one ssa: SafeStreetsApp |
			ssa.user = u
}

fact onlyRequestWithRunningTimeout {
	all ssa : SafeStreetsApp |
		all vrs: ssa.violationReportsSent |
			one vrr : ViolationReportRequest |
				vrr.violationReport = vrs and vrr.timeout = Running
}

// FIRST FUNCTION TO BE ANALYZED
pred reportViolation [ssa, ssa': SafeStreetsApp, vrr: ViolationReportRequest] {
	(	
		vrr.timeout = Running and
		let vr = vrr.violationReport |
			(
			vr.date != none and
			vr.time != none and
			vr.position != none and
			vr.reportImage != none and
			vr.type != none and
			vr.licensePlate != none and
			vr.status != none
			) 
	)
	implies
		ssa'.violationReportsSent = ssa.violationReportsSent + vrr.violationReport
}

// SafeStreets App doesn't send incomplete violation requests to the server.
assert NoIncompleteViolationReports {
	all ssa, ssa': SafeStreetsApp, vrr: ViolationReportRequest |
		reportViolation[ssa, ssa', vrr]
		implies
		all vr: ssa.violationReportsSent |
			(
				vr.date != none and
				vr.time != none and
				vr.position != none and
				vr.reportImage != none and
				vr.type != none and
				vr.licensePlate != none and
				vr.status != none
			)
}

// SafeStreets App doesn't send to the server violation requests that were not completed before the timeout ended.
assert NoTimedOutViolationReports {
	all ssa, ssa': SafeStreetsApp, vrr: ViolationReportRequest |
		vrr.timeout = Running and reportViolation[ssa, ssa', vrr]
		implies
		one vrs: ssa'.violationReportsSent |
			vrr.violationReport = vrs and vrr.timeout = Running 
}


//check NoIncompleteViolationReports for 5
//check NoTimedOutViolationReports for 5

//pred showWorld1 {}
//run showWorld1 {} for 2 but 0 Authority, 0 SafeStreetsAE, 0 SafeStreetsServer

////////////////////////////////////////////////////////////////////////////WORLD 2////////////////////////////////////////////////////////////////////////////////////
sig TypeOfAccident {}

sig Accident {
	date: one Date,
	time: one Time,
	position: one Position,
	type: one TypeOfAccident,
	licensePlate: one LicensePlate
}

// The key of an Accident is (date, time, position, type).
pred AccidentKey {
	all a1: Accident |
		no a2: Accident |
			a1 != a2 and
			a1.date = a2.date and
			a1.time = a2.time and
			a1.position = a2.position and
			a1.type = a2.type
}

sig AuthorityName, PostalCode {}
abstract sig Competence {}

// Two constraints are implicitly defined:
// - every Authority has exactly one name;
// - every authority has exactly one type of competence.
abstract sig Authority {
	name: one AuthorityName,
	typeOfCompetence: one Competence,
	areaOfCompetence: set PostalCode
}

fact associatedToAtLeastOneAuthority {
	all an: AuthorityName, c: Competence |
		some a:Authority |
			a.name = an or a.typeOfCompetence = c
} 

sig RegisteredAuthority extends Authority {}

// Every authority has a unique name.
fact AuthorityKey {
	all a1: Authority |
		no a2: Authority |
			a1 != a2 and a1.name = a2.name
}

sig SafeStreetsAE {
	violationsReported: set ViolationReport,
	accidentsToReport: set Accident,
	authority: one RegisteredAuthority
}

fact SafeStreetsAERegisteredAuthorityBijection {
	all ssae1: SafeStreetsAE |
		no ssae2: SafeStreetsAE |
			ssae1 != ssae2 and ssae1.authority = ssae2.authority
	all ra: RegisteredAuthority |
		one ssae: SafeStreetsAE |
			ssae.authority = ra
}

sig SafeStreetsServer {
	violationReports: set ViolationReport,
	accidents: set Accident
} { #SafeStreetsServer = 1 }

//Every ViolationReport in a SafeStreetsAE is also present on SafeStreetsServer.
fact AllReportsInAEAlsoInServer {
	all ssae: SafeStreetsAE |
		all vr: ssae.violationsReported |
			one vrServer : SafeStreetsServer.violationReports |
				vr in vrServer
}

pred ConfirmViolationReport[ssae, ssae': SafeStreetsAE, sss: SafeStreetsServer, vr: ViolationReport] {
	vr in ssae.violationsReported//and vr in sss, but this is guaranteed by fact AllReportsInAEAlsoInServer
	implies
	(
		ssae'.violationsReported = ssae.violationsReported - vr and
		(
			one vrs: SafeStreetsServer.violationReports |
				vrs = vr and vrs.status = Confirmed
		)
	)
}

assert ConsistentConfirmation {
	all ssae, ssae': SafeStreetsAE, sss: SafeStreetsServer, vr: ViolationReport |
		vr in ssae.violationsReported and
		ConfirmViolationReport[ssae, ssae', sss, vr]
		implies
		(
		vr not in ssae'.violationsReported and
			(
			one vrs: SafeStreetsServer.violationReports |
					vrs = vr and vrs.status = Confirmed
			)
		)
}

pred RefuseViolationReport[ssae, ssae': SafeStreetsAE, sss, sss': SafeStreetsServer, vr: ViolationReport] {
	vr in ssae.violationsReported//and vr in sss, but this is guaranteed by fact AllReportsInAEAlsoInServer
	implies
	(
		ssae'.violationsReported = ssae.violationsReported - vr and
		sss'.violationReports = sss.violationReports - vr
	)
}

assert ConsistentRejection {
	all ssae, ssae': SafeStreetsAE, sss, sss': SafeStreetsServer, vr: ViolationReport |
	vr in ssae.violationsReported and
	RefuseViolationReport[ssae, ssae', sss, sss', vr]
	implies
	(
		ssae'.violationsReported = ssae.violationsReported - vr and
		sss'.violationReports = sss.violationReports - vr
	)	
}

//check ConsistentRejection for 5 but 0 SafeStreetsApp, 0 User, 0 Accident, 0 ViolationReportRequest
//check ConsistentConfirmation for 5 but 0 SafeStreetsApp, 0 User, 0 Accident, 0 ViolationReportRequest

//pred showWorld2 {}
//run showWorld2 for 3 but 0 SafeStreetsApp, 0 User, 0 Accident, 0 ViolationReportRequest

////////////////////////////////////////////////////////////////////////////WORLD 3////////////////////////////////////////////////////////////////////////////////////
fact AllAccidentsReportedByAnAuthority {
	all a: Accident |
		one ssae: SafeStreetsAE |
			a in ssae.accidentsToReport
}

pred ReportAccident[ssae, ssae': SafeStreetsAE, sss, sss': SafeStreetsServer, a: Accident] {
	a in ssae.accidentsToReport
	implies
	ssae'.accidentsToReport = ssae.accidentsToReport - a and
	sss'.accidents = sss.accidents + a
}

assert ConsistentAccidentReport {
	all ssae, ssae': SafeStreetsAE, sss, sss': SafeStreetsServer, a: Accident |
		a in ssae.accidentsToReport and
		ReportAccident[ssae, ssae', sss, sss', a]
		implies
		ssae'.accidentsToReport = ssae.accidentsToReport - a and
		sss'.accidents = sss.accidents + a	
}

//check ConsistentAccidentReport for 5 but 0 SafeStreetsApp, 0 User, 0 ViolationReportRequest, 0 ViolationReport

pred showWorld3 {}
run showWorld3 for 3 but  0 SafeStreetsApp, 0 User, 0 ViolationReport, 0 ViolationReportRequest, 1 SafeStreetsAE
