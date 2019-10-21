;Copyright 2018 The MITRE Corporation. All rights reserved. Approved for public release. Distribution unlimited 17-2122.
; For more information on CALDERA, the automated adversary emulation system, visit https://github.com/mitre/caldera or email attack@mitre.org
; This has 6 hosts, 12 user, 1 admin per host, 2 active account per host
(define (problem p6_hosts_trial_15)
(:domain caldera)
(:objects
    id_adomain - observeddomain
    id_bbdomaincredential id_tdomaincredential id_bndomaincredential id_xdomaincredential id_bfdomaincredential id_bjdomaincredential id_ddomaincredential id_ldomaincredential id_bvdomaincredential id_brdomaincredential id_pdomaincredential id_hdomaincredential - observeddomaincredential
    str__bs str__cc str__cd str__cz str__u str__dn str__v str__michael str__bh str__dp str__ce str__jennifer str__m str__robert str__mary str__david str__bw str__e str__cl str__dm str__dl str__ck str__j str__alpha str__cx str__bo str__bc str__linda str__dg str__df str__cq str__bg str__b str__i str__james str__f str__r str__cj str__john str__z str__bl str__elizabeth str__bt str__bx str__cs str__patricia str__barbara str__bk str__cy str__bd str__de str__n str__q str__y str__cr str__bp str__william - string
    id_dsschtask id_dtschtask id_dqschtask id_duschtask id_dvschtask id_drschtask - observedschtask
    id_dhhost id_dahost id_cmhost id_cfhost id_cthost id_byhost - observedhost
    id_ekshare id_enshare id_elshare id_ejshare id_emshare id_eishare - observedshare
    num__73 num__87 num__88 num__67 num__53 num__81 num__80 num__60 num__52 num__66 num__74 num__59 - num
    id_wdomainuser id_kdomainuser id_bqdomainuser id_budomainuser id_bidomainuser id_odomainuser id_cdomainuser id_badomainuser id_bmdomainuser id_gdomainuser id_bedomainuser id_sdomainuser - observeddomainuser
    id_dyrat id_ebrat id_dxrat id_dzrat id_dwrat id_earat id_dorat - observedrat
    id_eefile id_ecfile id_egfile id_effile id_ehfile id_edfile - observedfile
    id_bztimedelta id_cgtimedelta id_cutimedelta id_dbtimedelta id_ditimedelta id_cntimedelta - observedtimedelta
)
(:init
    (knows id_byhost)
    (knows id_dorat)
    (knows_property id_byhost pfqdn)
    (knows_property id_dorat pexecutable)
    (knows_property id_dorat phost)
    (MEM_CACHED_DOMAIN_CREDS id_byhost id_bfdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_byhost id_bvdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cfhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cfhost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cmhost id_bbdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cmhost id_tdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cthost id_tdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cthost id_xdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dahost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dahost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dhhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_dhhost id_tdomaincredential)
    (MEM_DOMAIN_USER_ADMINS id_byhost id_bidomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cfhost id_bedomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cmhost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cthost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dahost id_badomainuser)
    (MEM_DOMAIN_USER_ADMINS id_dhhost id_badomainuser)
    (mem_hosts id_adomain id_byhost)
    (mem_hosts id_adomain id_cfhost)
    (mem_hosts id_adomain id_cmhost)
    (mem_hosts id_adomain id_cthost)
    (mem_hosts id_adomain id_dahost)
    (mem_hosts id_adomain id_dhhost)
    (prop_cred id_badomainuser id_bbdomaincredential)
    (prop_cred id_bedomainuser id_bfdomaincredential)
    (prop_cred id_bidomainuser id_bjdomaincredential)
    (prop_cred id_bmdomainuser id_bndomaincredential)
    (prop_cred id_bqdomainuser id_brdomaincredential)
    (prop_cred id_budomainuser id_bvdomaincredential)
    (prop_cred id_cdomainuser id_ddomaincredential)
    (prop_cred id_gdomainuser id_hdomaincredential)
    (prop_cred id_kdomainuser id_ldomaincredential)
    (prop_cred id_odomainuser id_pdomaincredential)
    (prop_cred id_sdomainuser id_tdomaincredential)
    (prop_cred id_wdomainuser id_xdomaincredential)
    (PROP_DC id_byhost no)
    (PROP_DC id_cfhost no)
    (PROP_DC id_cmhost yes)
    (PROP_DC id_cthost yes)
    (PROP_DC id_dahost no)
    (PROP_DC id_dhhost no)
    (PROP_DNS_DOMAIN id_adomain str__b)
    (PROP_DNS_DOMAIN_NAME id_byhost str__ce)
    (PROP_DNS_DOMAIN_NAME id_cfhost str__cl)
    (PROP_DNS_DOMAIN_NAME id_cmhost str__cs)
    (PROP_DNS_DOMAIN_NAME id_cthost str__cz)
    (PROP_DNS_DOMAIN_NAME id_dahost str__dg)
    (PROP_DNS_DOMAIN_NAME id_dhhost str__dn)
    (PROP_DOMAIN id_badomainuser id_adomain)
    (PROP_DOMAIN id_bbdomaincredential id_adomain)
    (PROP_DOMAIN id_bedomainuser id_adomain)
    (PROP_DOMAIN id_bfdomaincredential id_adomain)
    (PROP_DOMAIN id_bidomainuser id_adomain)
    (PROP_DOMAIN id_bjdomaincredential id_adomain)
    (PROP_DOMAIN id_bmdomainuser id_adomain)
    (PROP_DOMAIN id_bndomaincredential id_adomain)
    (PROP_DOMAIN id_bqdomainuser id_adomain)
    (PROP_DOMAIN id_brdomaincredential id_adomain)
    (PROP_DOMAIN id_budomainuser id_adomain)
    (PROP_DOMAIN id_bvdomaincredential id_adomain)
    (PROP_DOMAIN id_byhost id_adomain)
    (PROP_DOMAIN id_cdomainuser id_adomain)
    (PROP_DOMAIN id_cfhost id_adomain)
    (PROP_DOMAIN id_cmhost id_adomain)
    (PROP_DOMAIN id_cthost id_adomain)
    (PROP_DOMAIN id_ddomaincredential id_adomain)
    (PROP_DOMAIN id_dahost id_adomain)
    (PROP_DOMAIN id_dhhost id_adomain)
    (PROP_DOMAIN id_gdomainuser id_adomain)
    (PROP_DOMAIN id_hdomaincredential id_adomain)
    (PROP_DOMAIN id_kdomainuser id_adomain)
    (PROP_DOMAIN id_ldomaincredential id_adomain)
    (PROP_DOMAIN id_odomainuser id_adomain)
    (PROP_DOMAIN id_pdomaincredential id_adomain)
    (PROP_DOMAIN id_sdomainuser id_adomain)
    (PROP_DOMAIN id_tdomaincredential id_adomain)
    (PROP_DOMAIN id_wdomainuser id_adomain)
    (PROP_DOMAIN id_xdomaincredential id_adomain)
    (prop_elevated id_dorat yes)
    (prop_executable id_dorat str__dp)
    (PROP_FQDN id_byhost str__cc)
    (PROP_FQDN id_cfhost str__cj)
    (PROP_FQDN id_cmhost str__cq)
    (PROP_FQDN id_cthost str__cx)
    (PROP_FQDN id_dahost str__de)
    (PROP_FQDN id_dhhost str__dl)
    (prop_host id_bztimedelta id_byhost)
    (prop_host id_cgtimedelta id_cfhost)
    (prop_host id_cntimedelta id_cmhost)
    (prop_host id_cutimedelta id_cthost)
    (prop_host id_dbtimedelta id_dahost)
    (prop_host id_ditimedelta id_dhhost)
    (prop_host id_dorat id_byhost)
    (PROP_HOSTNAME id_byhost str__cd)
    (PROP_HOSTNAME id_cfhost str__ck)
    (PROP_HOSTNAME id_cmhost str__cr)
    (PROP_HOSTNAME id_cthost str__cy)
    (PROP_HOSTNAME id_dahost str__df)
    (PROP_HOSTNAME id_dhhost str__dm)
    (PROP_IS_GROUP id_badomainuser no)
    (PROP_IS_GROUP id_bedomainuser no)
    (PROP_IS_GROUP id_bidomainuser no)
    (PROP_IS_GROUP id_bmdomainuser no)
    (PROP_IS_GROUP id_bqdomainuser no)
    (PROP_IS_GROUP id_budomainuser no)
    (PROP_IS_GROUP id_cdomainuser no)
    (PROP_IS_GROUP id_gdomainuser no)
    (PROP_IS_GROUP id_kdomainuser no)
    (PROP_IS_GROUP id_odomainuser no)
    (PROP_IS_GROUP id_sdomainuser no)
    (PROP_IS_GROUP id_wdomainuser no)
    (PROP_MICROSECONDS id_bztimedelta num__52)
    (PROP_MICROSECONDS id_cgtimedelta num__59)
    (PROP_MICROSECONDS id_cntimedelta num__66)
    (PROP_MICROSECONDS id_cutimedelta num__73)
    (PROP_MICROSECONDS id_dbtimedelta num__80)
    (PROP_MICROSECONDS id_ditimedelta num__87)
    (PROP_PASSWORD id_bbdomaincredential str__bc)
    (PROP_PASSWORD id_bfdomaincredential str__bg)
    (PROP_PASSWORD id_bjdomaincredential str__bk)
    (PROP_PASSWORD id_bndomaincredential str__bo)
    (PROP_PASSWORD id_brdomaincredential str__bs)
    (PROP_PASSWORD id_bvdomaincredential str__bw)
    (PROP_PASSWORD id_ddomaincredential str__e)
    (PROP_PASSWORD id_hdomaincredential str__i)
    (PROP_PASSWORD id_ldomaincredential str__m)
    (PROP_PASSWORD id_pdomaincredential str__q)
    (PROP_PASSWORD id_tdomaincredential str__u)
    (PROP_PASSWORD id_xdomaincredential str__y)
    (PROP_SECONDS id_bztimedelta num__53)
    (PROP_SECONDS id_cgtimedelta num__60)
    (PROP_SECONDS id_cntimedelta num__67)
    (PROP_SECONDS id_cutimedelta num__74)
    (PROP_SECONDS id_dbtimedelta num__81)
    (PROP_SECONDS id_ditimedelta num__88)
    (PROP_SID id_badomainuser str__bd)
    (PROP_SID id_bedomainuser str__bh)
    (PROP_SID id_bidomainuser str__bl)
    (PROP_SID id_bmdomainuser str__bp)
    (PROP_SID id_bqdomainuser str__bt)
    (PROP_SID id_budomainuser str__bx)
    (PROP_SID id_cdomainuser str__f)
    (PROP_SID id_gdomainuser str__j)
    (PROP_SID id_kdomainuser str__n)
    (PROP_SID id_odomainuser str__r)
    (PROP_SID id_sdomainuser str__v)
    (PROP_SID id_wdomainuser str__z)
    (PROP_TIMEDELTA id_byhost id_bztimedelta)
    (PROP_TIMEDELTA id_cfhost id_cgtimedelta)
    (PROP_TIMEDELTA id_cmhost id_cntimedelta)
    (PROP_TIMEDELTA id_cthost id_cutimedelta)
    (PROP_TIMEDELTA id_dahost id_dbtimedelta)
    (PROP_TIMEDELTA id_dhhost id_ditimedelta)
    (PROP_USER id_bbdomaincredential id_badomainuser)
    (PROP_USER id_bfdomaincredential id_bedomainuser)
    (PROP_USER id_bjdomaincredential id_bidomainuser)
    (PROP_USER id_bndomaincredential id_bmdomainuser)
    (PROP_USER id_brdomaincredential id_bqdomainuser)
    (PROP_USER id_bvdomaincredential id_budomainuser)
    (PROP_USER id_ddomaincredential id_cdomainuser)
    (PROP_USER id_hdomaincredential id_gdomainuser)
    (PROP_USER id_ldomaincredential id_kdomainuser)
    (PROP_USER id_pdomaincredential id_odomainuser)
    (PROP_USER id_tdomaincredential id_sdomainuser)
    (PROP_USER id_xdomaincredential id_wdomainuser)
    (PROP_USERNAME id_badomainuser str__michael)
    (PROP_USERNAME id_bedomainuser str__barbara)
    (PROP_USERNAME id_bidomainuser str__william)
    (PROP_USERNAME id_bmdomainuser str__elizabeth)
    (PROP_USERNAME id_bqdomainuser str__david)
    (PROP_USERNAME id_budomainuser str__jennifer)
    (PROP_USERNAME id_cdomainuser str__james)
    (PROP_USERNAME id_gdomainuser str__mary)
    (PROP_USERNAME id_kdomainuser str__john)
    (PROP_USERNAME id_odomainuser str__patricia)
    (PROP_USERNAME id_sdomainuser str__robert)
    (PROP_USERNAME id_wdomainuser str__linda)
    (PROP_WINDOWS_DOMAIN id_adomain str__alpha)
)
(:goal
(and
    (prop_host id_earat id_cmhost)
    (prop_host id_dyrat id_cthost)
    (prop_host id_ebrat id_cfhost)
    (prop_host id_dxrat id_dhhost)
    (prop_host id_dzrat id_dahost)
)
)
)