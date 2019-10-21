;Copyright 2018 The MITRE Corporation. All rights reserved. Approved for public release. Distribution unlimited 17-2122.
; For more information on CALDERA, the automated adversary emulation system, visit https://github.com/mitre/caldera or email attack@mitre.org
; This has 5 hosts, 10 user, 1 admin per host, 3 active account per host
(define (problem p5_hosts_trial_12)
(:domain caldera)
(:objects
    id_djschtask id_dgschtask id_dhschtask id_dkschtask id_dischtask - observedschtask
    id_adomain - observeddomain
    id_dufile id_dtfile id_drfile id_dsfile id_dqfile - observedfile
    id_badomainuser id_bmdomainuser id_gdomainuser id_sdomainuser id_wdomainuser id_kdomainuser id_bedomainuser id_odomainuser id_bidomainuser id_cdomainuser - observeddomainuser
    num__44 num__72 num__59 num__66 num__58 num__52 num__73 num__51 num__65 num__45 - num
    id_dorat id_dnrat id_dmrat id_czrat id_dlrat id_dprat - observedrat
    id_deshare id_dbshare id_dfshare id_ddshare id_dcshare - observedshare
    id_ddomaincredential id_bndomaincredential id_pdomaincredential id_ldomaincredential id_hdomaincredential id_bfdomaincredential id_xdomaincredential id_bjdomaincredential id_bbdomaincredential id_tdomaincredential - observeddomaincredential
    str__robert str__e str__cc str__john str__u str__bu str__bw str__cy str__bp str__william str__cw str__patricia str__n str__mary str__james str__linda str__elizabeth str__b str__bh str__j str__q str__cr str__f str__cb str__y str__bo str__bc str__z str__cq str__r str__m str__bd str__cj str__bg str__bl str__v str__da str__i str__bk str__ci str__cx str__barbara str__cp str__cd str__alpha str__bv str__ck str__michael - string
    id_bytimedelta id_brtimedelta id_cmtimedelta id_cttimedelta id_cftimedelta - observedtimedelta
    id_cehost id_bxhost id_clhost id_bqhost id_cshost - observedhost
)
(:init
    (knows id_bqhost)
    (knows id_czrat)
    (knows_property id_bqhost pfqdn)
    (knows_property id_czrat pexecutable)
    (knows_property id_czrat phost)
    (MEM_CACHED_DOMAIN_CREDS id_bqhost id_bjdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bqhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bqhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bxhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bxhost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bxhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cehost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cehost id_ldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cehost id_xdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_clhost id_bfdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_clhost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_clhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cshost id_bbdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cshost id_bjdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_cshost id_bndomaincredential)
    (MEM_DOMAIN_USER_ADMINS id_bqhost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bxhost id_bedomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cehost id_bidomainuser)
    (MEM_DOMAIN_USER_ADMINS id_clhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_cshost id_gdomainuser)
    (mem_hosts id_adomain id_bqhost)
    (mem_hosts id_adomain id_bxhost)
    (mem_hosts id_adomain id_cehost)
    (mem_hosts id_adomain id_clhost)
    (mem_hosts id_adomain id_cshost)
    (prop_cred id_badomainuser id_bbdomaincredential)
    (prop_cred id_bedomainuser id_bfdomaincredential)
    (prop_cred id_bidomainuser id_bjdomaincredential)
    (prop_cred id_bmdomainuser id_bndomaincredential)
    (prop_cred id_cdomainuser id_ddomaincredential)
    (prop_cred id_gdomainuser id_hdomaincredential)
    (prop_cred id_kdomainuser id_ldomaincredential)
    (prop_cred id_odomainuser id_pdomaincredential)
    (prop_cred id_sdomainuser id_tdomaincredential)
    (prop_cred id_wdomainuser id_xdomaincredential)
    (PROP_DC id_bqhost no)
    (PROP_DC id_bxhost no)
    (PROP_DC id_cehost yes)
    (PROP_DC id_clhost yes)
    (PROP_DC id_cshost no)
    (PROP_DNS_DOMAIN id_adomain str__b)
    (PROP_DNS_DOMAIN_NAME id_bqhost str__bv)
    (PROP_DNS_DOMAIN_NAME id_bxhost str__cc)
    (PROP_DNS_DOMAIN_NAME id_cehost str__cj)
    (PROP_DNS_DOMAIN_NAME id_clhost str__cq)
    (PROP_DNS_DOMAIN_NAME id_cshost str__cx)
    (PROP_DOMAIN id_badomainuser id_adomain)
    (PROP_DOMAIN id_bbdomaincredential id_adomain)
    (PROP_DOMAIN id_bedomainuser id_adomain)
    (PROP_DOMAIN id_bfdomaincredential id_adomain)
    (PROP_DOMAIN id_bidomainuser id_adomain)
    (PROP_DOMAIN id_bjdomaincredential id_adomain)
    (PROP_DOMAIN id_bmdomainuser id_adomain)
    (PROP_DOMAIN id_bndomaincredential id_adomain)
    (PROP_DOMAIN id_bqhost id_adomain)
    (PROP_DOMAIN id_bxhost id_adomain)
    (PROP_DOMAIN id_cdomainuser id_adomain)
    (PROP_DOMAIN id_cehost id_adomain)
    (PROP_DOMAIN id_clhost id_adomain)
    (PROP_DOMAIN id_cshost id_adomain)
    (PROP_DOMAIN id_ddomaincredential id_adomain)
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
    (prop_elevated id_czrat yes)
    (prop_executable id_czrat str__da)
    (PROP_FQDN id_bqhost str__bu)
    (PROP_FQDN id_bxhost str__cb)
    (PROP_FQDN id_cehost str__ci)
    (PROP_FQDN id_clhost str__cp)
    (PROP_FQDN id_cshost str__cw)
    (prop_host id_brtimedelta id_bqhost)
    (prop_host id_bytimedelta id_bxhost)
    (prop_host id_cftimedelta id_cehost)
    (prop_host id_cmtimedelta id_clhost)
    (prop_host id_cttimedelta id_cshost)
    (prop_host id_czrat id_bqhost)
    (PROP_HOSTNAME id_bqhost str__bw)
    (PROP_HOSTNAME id_bxhost str__cd)
    (PROP_HOSTNAME id_cehost str__ck)
    (PROP_HOSTNAME id_clhost str__cr)
    (PROP_HOSTNAME id_cshost str__cy)
    (PROP_IS_GROUP id_badomainuser no)
    (PROP_IS_GROUP id_bedomainuser no)
    (PROP_IS_GROUP id_bidomainuser no)
    (PROP_IS_GROUP id_bmdomainuser no)
    (PROP_IS_GROUP id_cdomainuser no)
    (PROP_IS_GROUP id_gdomainuser no)
    (PROP_IS_GROUP id_kdomainuser no)
    (PROP_IS_GROUP id_odomainuser no)
    (PROP_IS_GROUP id_sdomainuser no)
    (PROP_IS_GROUP id_wdomainuser no)
    (PROP_MICROSECONDS id_brtimedelta num__44)
    (PROP_MICROSECONDS id_bytimedelta num__51)
    (PROP_MICROSECONDS id_cftimedelta num__58)
    (PROP_MICROSECONDS id_cmtimedelta num__65)
    (PROP_MICROSECONDS id_cttimedelta num__72)
    (PROP_PASSWORD id_bbdomaincredential str__bc)
    (PROP_PASSWORD id_bfdomaincredential str__bg)
    (PROP_PASSWORD id_bjdomaincredential str__bk)
    (PROP_PASSWORD id_bndomaincredential str__bo)
    (PROP_PASSWORD id_ddomaincredential str__e)
    (PROP_PASSWORD id_hdomaincredential str__i)
    (PROP_PASSWORD id_ldomaincredential str__m)
    (PROP_PASSWORD id_pdomaincredential str__q)
    (PROP_PASSWORD id_tdomaincredential str__u)
    (PROP_PASSWORD id_xdomaincredential str__y)
    (PROP_SECONDS id_brtimedelta num__45)
    (PROP_SECONDS id_bytimedelta num__52)
    (PROP_SECONDS id_cftimedelta num__59)
    (PROP_SECONDS id_cmtimedelta num__66)
    (PROP_SECONDS id_cttimedelta num__73)
    (PROP_SID id_badomainuser str__bd)
    (PROP_SID id_bedomainuser str__bh)
    (PROP_SID id_bidomainuser str__bl)
    (PROP_SID id_bmdomainuser str__bp)
    (PROP_SID id_cdomainuser str__f)
    (PROP_SID id_gdomainuser str__j)
    (PROP_SID id_kdomainuser str__n)
    (PROP_SID id_odomainuser str__r)
    (PROP_SID id_sdomainuser str__v)
    (PROP_SID id_wdomainuser str__z)
    (PROP_TIMEDELTA id_bqhost id_brtimedelta)
    (PROP_TIMEDELTA id_bxhost id_bytimedelta)
    (PROP_TIMEDELTA id_cehost id_cftimedelta)
    (PROP_TIMEDELTA id_clhost id_cmtimedelta)
    (PROP_TIMEDELTA id_cshost id_cttimedelta)
    (PROP_USER id_bbdomaincredential id_badomainuser)
    (PROP_USER id_bfdomaincredential id_bedomainuser)
    (PROP_USER id_bjdomaincredential id_bidomainuser)
    (PROP_USER id_bndomaincredential id_bmdomainuser)
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
    (prop_host id_dnrat id_cshost)
    (prop_host id_dlrat id_clhost)
    (prop_host id_dmrat id_cehost)
    (prop_host id_dprat id_bxhost)
)
)
)