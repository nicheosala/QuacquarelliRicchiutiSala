abstract sig Timeout {}

sig Running, Ended extends Timeout {} 

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

sig ViolationReportRequest {
	violationReport: one ViolationReport,
	timeout: one Timeout
}

fact ViolationReportAndRequestBijection {
	all vrr1: ViolationReportRequest |
		no vrr2: ViolationReportRequest |
			vrr1 != vrr2 and vrr1.violationReport = vrr2.violationReport
	all vr: ViolationReport |
		one vrr: ViolationReportRequest |
			vr = vrr.violationReport
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

fact onlyRequestWithRunningTimeout {
	all ssa : SafeStreetsApp |
		all vrs: ssa.violationReportsSent |
			one vrr : ViolationReportRequest |
				vrr.violationReport = vrs and vrr.timeout = Running
}

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

// SafeStreets App doesn't send violation requests to the server that are incomplete.
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


check NoIncompleteViolationReports for 5
check NoTimedOutViolationReports for 5

pred show {}
run show {} for 2


