////////////////////////////////////////////////////////////////AUTHORITY////////////////////////////////////////////////////////////////
sig AuthorityName, PostalCode {}

abstract sig Competence {}
one sig Municipal, Provincial, Statal extends Competence {}

// Two constraints are implicitly defined:
// - every Authority has exactly one name;
// - every authority has exactly one type of competence.
abstract sig Authority {
	name: one AuthorityName,
	typeOfCompetence: one Competence,
	areaOfCompetence: set PostalCode
}

sig RegisteredAuthority extends Authority {}

// Every authority has a unique name.
fact AuthorityKey {
	all a1: Authority |
		no a2: Authority |
			a1 != a2 and a1.name = a2.name
}

// Every authority has competence on at least one postal code.
fact AuthorityNotEmptyAreaOfCompetence {
	all a: Authority |
		#a.areaOfCompetence >= 1
}

//There are no different authorities with the same area of competence.
fact AuthorityNotSameareaOfCompetence {
	all a1: Authority |
		no a2: Authority |
			a1 != a2 and a1.areaOfCompetence = a2.areaOfCompetence
}

//TODO vincoli sul tipo di competence!

////////////////////////////////////////////////////////////////VIOLATION REPORT////////////////////////////////////////////////////////////////
sig Date, Time, Position, Image, TypeOfViolation, LicensePlate, ReportStatus {}

sig ViolationReport {
	date: one Date,
	time: one Time,
	position: one Position,
	reportImage: one Image,
	type: one TypeOfViolation,
	licensePlate: one LicensePlate,
	status: one ReportStatus
}

//The public key (== visible to all individuals)  of a ViolationReport is (date, time, position, type).
fact ViolationReportKey {
	all vr1: ViolationReport |
		no vr2: ViolationReport |
			vr1 != vr2 and
			vr1.date = vr2.date and
			vr1.time = vr2.time and
			vr1.position = vr2.position and
			vr1.type = vr2.type
}

// TODO Define ReportStatus possible values.

////////////////////////////////////////////////////////////////ACCIDENT////////////////////////////////////////////////////////////////
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


////////////////////////////////////////////////////////////////SAFESTREETS SERVER////////////////////////////////////////////////////////////////
sig SafeStreetsServer {
	violationReports: set ViolationReport,
	accidents: set Accident
} { #SafeStreetsServer = 1 }

////////////////////////////////////////////////////////////////SAFESTREETS AE////////////////////////////////////////////////////////////////
sig SafeStreetsAE {
	violationReportsChecked: set ViolationReport,
	accidentsReported: set Accident,
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

sig SafeStreetsApp {
	violationReportsSent: set ViolationReport,
	user: one User
}

sig User {}

fact SafeStreetsAppUserBijection {
	all ssa1: SafeStreetsApp |
		no ssa2: SafeStreetsApp |
			ssa1 != ssa2 and ssa1.user = ssa2.user
	all u: User |
		one ssa: SafeStreetsApp |
			ssa.user = u
}

pred EveryAccidentHasBeenReportedByARegisteredAuthority {
	all accident: Accident |
		one sfae: SafeStreetsAE |
			accident in sfae.accidentsReported
}

run EveryAccidentHasBeenReportedByARegisteredAuthority for 3 but 1 SafeStreetsAE, 1 ViolationReport, 1 Accident, 0 SafeStreetsApp

pred EveryViolationReportHasBeenReportedByAUser {}
pred EveryRegisteredAuthorityReceivesOnlyCompetentViolationReports {}
