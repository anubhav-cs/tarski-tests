;Copyright 2018 The MITRE Corporation. All rights reserved. Approved for public release. Distribution unlimited 17-2122.
; For more information on CALDERA, the automated adversary emulation system, visit https://github.com/mitre/caldera or email attack@mitre.org
; This has 11 hosts, 5 user, 2 admin per host, 2 active account per host
(define (problem p11_hosts_trial_5)
(:domain caldera)
(:objects
    id_edshare id_dyshare id_efshare id_dzshare id_dxshare id_ebshare id_eashare id_ehshare id_egshare id_ecshare id_eeshare - observedshare
    id_ldomaincredential id_tdomaincredential id_hdomaincredential id_ddomaincredential id_pdomaincredential - observeddomaincredential
    id_kdomainuser id_gdomainuser id_cdomainuser id_odomainuser id_sdomainuser - observeddomainuser
    id_bztimedelta id_dptimedelta id_cgtimedelta id_betimedelta id_xtimedelta id_cutimedelta id_dbtimedelta id_bstimedelta id_ditimedelta id_cntimedelta id_bltimedelta - observedtimedelta
    id_byhost id_brhost id_dhhost id_dahost id_bdhost id_cmhost id_cthost id_bkhost id_dohost id_whost id_cfhost - observedhost
    num__80 num__87 num__32 num__39 num__81 num__24 num__59 num__73 num__45 num__60 num__88 num__53 num__52 num__94 num__46 num__25 num__66 num__38 num__31 num__74 num__67 num__95 - num
    id_erfile id_ejfile id_ekfile id_elfile id_emfile id_eqfile id_eifile id_eofile id_epfile id_esfile id_enfile - observedfile
    id_adomain - observeddomain
    id_etrat id_fbrat id_exrat id_dvrat id_eurat id_ewrat id_farat id_evrat id_ezrat id_fdrat id_eyrat id_fcrat - observedrat
    str__e str__ba str__john str__cq str__ce str__de str__b str__bw str__du str__bb str__v str__bq str__ds str__q str__j str__bh str__mary str__f str__bp str__cc str__cl str__cs str__df str__dw str__ck str__alpha str__dg str__cd str__cx str__r str__robert str__i str__u str__james str__bv str__dt str__n str__dl str__dm str__bc str__cj str__cy str__cr str__cz str__patricia str__bj str__bx str__bo str__bi str__dn str__m - string
    id_fgschtask id_fhschtask id_foschtask id_feschtask id_fmschtask id_fjschtask id_ffschtask id_fkschtask id_fnschtask id_flschtask id_fischtask - observedschtask
)
(:init
    (knows id_dohost)
    (knows id_dvrat)
    (knows_property id_dohost pfqdn)
    (knows_property id_dvrat pexecutable)
    (knows_property id_dvrat phost)
    (MEM_CACHED_DOMAIN_CREDS id_bdhost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bdhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bkhost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bkhost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_brhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_brhost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_byhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_byhost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cfhost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cfhost id_tdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cmhost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cmhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cthost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cthost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dahost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dahost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dhhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dhhost id_tdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dohost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dohost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_whost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_whost id_pdomaincredential)
    (MEM_DOMAIN_USER_ADMINS id_bdhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bdhost id_odomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bkhost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bkhost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_brhost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_brhost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_byhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_byhost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cfhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cfhost id_sdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cmhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cmhost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cthost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cthost id_sdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dahost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dahost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dhhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dhhost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dohost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dohost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_whost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_whost id_odomainuser)
    (mem_hosts id_adomain id_bdhost)
    (mem_hosts id_adomain id_bkhost)
    (mem_hosts id_adomain id_brhost)
    (mem_hosts id_adomain id_byhost)
    (mem_hosts id_adomain id_cfhost)
    (mem_hosts id_adomain id_cmhost)
    (mem_hosts id_adomain id_cthost)
    (mem_hosts id_adomain id_dahost)
    (mem_hosts id_adomain id_dhhost)
    (mem_hosts id_adomain id_dohost)
    (mem_hosts id_adomain id_whost)
    (prop_cred id_cdomainuser id_ddomaincredential)
    (prop_cred id_gdomainuser id_hdomaincredential)
    (prop_cred id_kdomainuser id_ldomaincredential)
    (prop_cred id_odomainuser id_pdomaincredential)
    (prop_cred id_sdomainuser id_tdomaincredential)
    (PROP_DC id_bdhost yes)
    (PROP_DC id_bkhost no)
    (PROP_DC id_brhost no)
    (PROP_DC id_byhost no)
    (PROP_DC id_cfhost no)
    (PROP_DC id_cmhost no)
    (PROP_DC id_cthost yes)
    (PROP_DC id_dahost no)
    (PROP_DC id_dhhost no)
    (PROP_DC id_dohost no)
    (PROP_DC id_whost no)
    (PROP_DNS_DOMAIN id_adomain str__b)
    (PROP_DNS_DOMAIN_NAME id_bdhost str__bh)
    (PROP_DNS_DOMAIN_NAME id_bkhost str__bo)
    (PROP_DNS_DOMAIN_NAME id_brhost str__bv)
    (PROP_DNS_DOMAIN_NAME id_byhost str__cc)
    (PROP_DNS_DOMAIN_NAME id_cfhost str__cj)
    (PROP_DNS_DOMAIN_NAME id_cmhost str__cq)
    (PROP_DNS_DOMAIN_NAME id_cthost str__cx)
    (PROP_DNS_DOMAIN_NAME id_dahost str__de)
    (PROP_DNS_DOMAIN_NAME id_dhhost str__dl)
    (PROP_DNS_DOMAIN_NAME id_dohost str__ds)
    (PROP_DNS_DOMAIN_NAME id_whost str__ba)
    (PROP_DOMAIN id_bdhost id_adomain)
    (PROP_DOMAIN id_bkhost id_adomain)
    (PROP_DOMAIN id_brhost id_adomain)
    (PROP_DOMAIN id_byhost id_adomain)
    (PROP_DOMAIN id_cdomainuser id_adomain)
    (PROP_DOMAIN id_cfhost id_adomain)
    (PROP_DOMAIN id_cmhost id_adomain)
    (PROP_DOMAIN id_cthost id_adomain)
    (PROP_DOMAIN id_ddomaincredential id_adomain)
    (PROP_DOMAIN id_dahost id_adomain)
    (PROP_DOMAIN id_dhhost id_adomain)
    (PROP_DOMAIN id_dohost id_adomain)
    (PROP_DOMAIN id_gdomainuser id_adomain)
    (PROP_DOMAIN id_hdomaincredential id_adomain)
    (PROP_DOMAIN id_kdomainuser id_adomain)
    (PROP_DOMAIN id_ldomaincredential id_adomain)
    (PROP_DOMAIN id_odomainuser id_adomain)
    (PROP_DOMAIN id_pdomaincredential id_adomain)
    (PROP_DOMAIN id_sdomainuser id_adomain)
    (PROP_DOMAIN id_tdomaincredential id_adomain)
    (PROP_DOMAIN id_whost id_adomain)
    (prop_elevated id_dvrat yes)
    (prop_executable id_dvrat str__dw)
    (PROP_FQDN id_bdhost str__bi)
    (PROP_FQDN id_bkhost str__bp)
    (PROP_FQDN id_brhost str__bw)
    (PROP_FQDN id_byhost str__cd)
    (PROP_FQDN id_cfhost str__ck)
    (PROP_FQDN id_cmhost str__cr)
    (PROP_FQDN id_cthost str__cy)
    (PROP_FQDN id_dahost str__df)
    (PROP_FQDN id_dhhost str__dm)
    (PROP_FQDN id_dohost str__dt)
    (PROP_FQDN id_whost str__bb)
    (prop_host id_betimedelta id_bdhost)
    (prop_host id_bltimedelta id_bkhost)
    (prop_host id_bstimedelta id_brhost)
    (prop_host id_bztimedelta id_byhost)
    (prop_host id_cgtimedelta id_cfhost)
    (prop_host id_cntimedelta id_cmhost)
    (prop_host id_cutimedelta id_cthost)
    (prop_host id_dbtimedelta id_dahost)
    (prop_host id_ditimedelta id_dhhost)
    (prop_host id_dptimedelta id_dohost)
    (prop_host id_dvrat id_dohost)
    (prop_host id_xtimedelta id_whost)
    (PROP_HOSTNAME id_bdhost str__bj)
    (PROP_HOSTNAME id_bkhost str__bq)
    (PROP_HOSTNAME id_brhost str__bx)
    (PROP_HOSTNAME id_byhost str__ce)
    (PROP_HOSTNAME id_cfhost str__cl)
    (PROP_HOSTNAME id_cmhost str__cs)
    (PROP_HOSTNAME id_cthost str__cz)
    (PROP_HOSTNAME id_dahost str__dg)
    (PROP_HOSTNAME id_dhhost str__dn)
    (PROP_HOSTNAME id_dohost str__du)
    (PROP_HOSTNAME id_whost str__bc)
    (PROP_IS_GROUP id_cdomainuser no)
    (PROP_IS_GROUP id_gdomainuser no)
    (PROP_IS_GROUP id_kdomainuser no)
    (PROP_IS_GROUP id_odomainuser no)
    (PROP_IS_GROUP id_sdomainuser no)
    (PROP_MICROSECONDS id_betimedelta num__31)
    (PROP_MICROSECONDS id_bltimedelta num__38)
    (PROP_MICROSECONDS id_bstimedelta num__45)
    (PROP_MICROSECONDS id_bztimedelta num__52)
    (PROP_MICROSECONDS id_cgtimedelta num__59)
    (PROP_MICROSECONDS id_cntimedelta num__66)
    (PROP_MICROSECONDS id_cutimedelta num__73)
    (PROP_MICROSECONDS id_dbtimedelta num__80)
    (PROP_MICROSECONDS id_ditimedelta num__87)
    (PROP_MICROSECONDS id_dptimedelta num__94)
    (PROP_MICROSECONDS id_xtimedelta num__24)
    (PROP_PASSWORD id_ddomaincredential str__e)
    (PROP_PASSWORD id_hdomaincredential str__i)
    (PROP_PASSWORD id_ldomaincredential str__m)
    (PROP_PASSWORD id_pdomaincredential str__q)
    (PROP_PASSWORD id_tdomaincredential str__u)
    (PROP_SECONDS id_betimedelta num__32)
    (PROP_SECONDS id_bltimedelta num__39)
    (PROP_SECONDS id_bstimedelta num__46)
    (PROP_SECONDS id_bztimedelta num__53)
    (PROP_SECONDS id_cgtimedelta num__60)
    (PROP_SECONDS id_cntimedelta num__67)
    (PROP_SECONDS id_cutimedelta num__74)
    (PROP_SECONDS id_dbtimedelta num__81)
    (PROP_SECONDS id_ditimedelta num__88)
    (PROP_SECONDS id_dptimedelta num__95)
    (PROP_SECONDS id_xtimedelta num__25)
    (PROP_SID id_cdomainuser str__f)
    (PROP_SID id_gdomainuser str__j)
    (PROP_SID id_kdomainuser str__n)
    (PROP_SID id_odomainuser str__r)
    (PROP_SID id_sdomainuser str__v)
    (PROP_TIMEDELTA id_bdhost id_betimedelta)
    (PROP_TIMEDELTA id_bkhost id_bltimedelta)
    (PROP_TIMEDELTA id_brhost id_bstimedelta)
    (PROP_TIMEDELTA id_byhost id_bztimedelta)
    (PROP_TIMEDELTA id_cfhost id_cgtimedelta)
    (PROP_TIMEDELTA id_cmhost id_cntimedelta)
    (PROP_TIMEDELTA id_cthost id_cutimedelta)
    (PROP_TIMEDELTA id_dahost id_dbtimedelta)
    (PROP_TIMEDELTA id_dhhost id_ditimedelta)
    (PROP_TIMEDELTA id_dohost id_dptimedelta)
    (PROP_TIMEDELTA id_whost id_xtimedelta)
    (PROP_USER id_ddomaincredential id_cdomainuser)
    (PROP_USER id_hdomaincredential id_gdomainuser)
    (PROP_USER id_ldomaincredential id_kdomainuser)
    (PROP_USER id_pdomaincredential id_odomainuser)
    (PROP_USER id_tdomaincredential id_sdomainuser)
    (PROP_USERNAME id_cdomainuser str__james)
    (PROP_USERNAME id_gdomainuser str__mary)
    (PROP_USERNAME id_kdomainuser str__john)
    (PROP_USERNAME id_odomainuser str__patricia)
    (PROP_USERNAME id_sdomainuser str__robert)
    (PROP_WINDOWS_DOMAIN id_adomain str__alpha)
)
(:goal
(and
    (prop_host id_fcrat id_cfhost)
    (prop_host id_etrat id_byhost)
    (prop_host id_fbrat id_brhost)
    (prop_host id_exrat id_dhhost)
    (prop_host id_eurat id_dahost)
    (prop_host id_ewrat id_bdhost)
    (prop_host id_farat id_cmhost)
    (prop_host id_evrat id_cthost)
    (prop_host id_ezrat id_bkhost)
    (prop_host id_fdrat id_whost)
)
)
)