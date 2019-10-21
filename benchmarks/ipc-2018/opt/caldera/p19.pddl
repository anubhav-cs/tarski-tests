;Copyright 2018 The MITRE Corporation. All rights reserved. Approved for public release. Distribution unlimited 17-2122.
; For more information on CALDERA, the automated adversary emulation system, visit https://github.com/mitre/caldera or email attack@mitre.org
; This has 6 hosts, 2 user, 2 admin per host, 2 active account per host
(define (problem p6_hosts_trial_2)
(:domain caldera)
(:objects
    id_hdomaincredential id_ddomaincredential - observeddomaincredential
    id_carat id_cerat id_chrat id_cdrat id_cgrat id_cfrat id_ccrat - observedrat
    id_bntimedelta id_ztimedelta id_stimedelta id_butimedelta id_bgtimedelta id_ltimedelta - observedtimedelta
    str__f str__b str__mary str__j str__bj str__bz str__bs str__q str__br str__x str__cb str__w str__bd str__p str__o str__e str__bc str__by str__bk str__alpha str__james str__bq str__be str__i str__bx str__v str__bl - string
    id_rhost id_bthost id_khost id_yhost id_bmhost id_bfhost - observedhost
    id_cdomainuser id_gdomainuser - observeddomainuser
    num__19 num__34 num__47 num__20 num__27 num__12 num__48 num__13 num__41 num__33 num__26 num__40 - num
    id_cjschtask id_cmschtask id_cnschtask id_ckschtask id_clschtask id_cischtask - observedschtask
    id_crfile id_ctfile id_cpfile id_csfile id_cqfile id_cofile - observedfile
    id_adomain - observeddomain
    id_czshare id_cxshare id_cvshare id_cyshare id_cwshare id_cushare - observedshare
)
(:init
    (knows id_bfhost)
    (knows id_carat)
    (knows_property id_bfhost pfqdn)
    (knows_property id_carat pexecutable)
    (knows_property id_carat phost)
    (MEM_CACHED_DOMAIN_CREDS id_bfhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bfhost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bmhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bmhost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bthost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bthost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_khost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_khost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_rhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_rhost id_hdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_yhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_yhost id_hdomaincredential)
    (MEM_DOMAIN_USER_ADMINS id_bfhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bfhost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bmhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bmhost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bthost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bthost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_khost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_khost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_rhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_rhost id_gdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_yhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_yhost id_gdomainuser)
    (mem_hosts id_adomain id_bfhost)
    (mem_hosts id_adomain id_bmhost)
    (mem_hosts id_adomain id_bthost)
    (mem_hosts id_adomain id_khost)
    (mem_hosts id_adomain id_rhost)
    (mem_hosts id_adomain id_yhost)
    (prop_cred id_cdomainuser id_ddomaincredential)
    (prop_cred id_gdomainuser id_hdomaincredential)
    (PROP_DC id_bfhost yes)
    (PROP_DC id_bmhost no)
    (PROP_DC id_bthost no)
    (PROP_DC id_khost no)
    (PROP_DC id_rhost no)
    (PROP_DC id_yhost no)
    (PROP_DNS_DOMAIN id_adomain str__b)
    (PROP_DNS_DOMAIN_NAME id_bfhost str__bl)
    (PROP_DNS_DOMAIN_NAME id_bmhost str__bs)
    (PROP_DNS_DOMAIN_NAME id_bthost str__bz)
    (PROP_DNS_DOMAIN_NAME id_khost str__q)
    (PROP_DNS_DOMAIN_NAME id_rhost str__x)
    (PROP_DNS_DOMAIN_NAME id_yhost str__be)
    (PROP_DOMAIN id_bfhost id_adomain)
    (PROP_DOMAIN id_bmhost id_adomain)
    (PROP_DOMAIN id_bthost id_adomain)
    (PROP_DOMAIN id_cdomainuser id_adomain)
    (PROP_DOMAIN id_ddomaincredential id_adomain)
    (PROP_DOMAIN id_gdomainuser id_adomain)
    (PROP_DOMAIN id_hdomaincredential id_adomain)
    (PROP_DOMAIN id_khost id_adomain)
    (PROP_DOMAIN id_rhost id_adomain)
    (PROP_DOMAIN id_yhost id_adomain)
    (prop_elevated id_carat yes)
    (prop_executable id_carat str__cb)
    (PROP_FQDN id_bfhost str__bk)
    (PROP_FQDN id_bmhost str__br)
    (PROP_FQDN id_bthost str__by)
    (PROP_FQDN id_khost str__p)
    (PROP_FQDN id_rhost str__w)
    (PROP_FQDN id_yhost str__bd)
    (prop_host id_bgtimedelta id_bfhost)
    (prop_host id_bntimedelta id_bmhost)
    (prop_host id_butimedelta id_bthost)
    (prop_host id_carat id_bfhost)
    (prop_host id_ltimedelta id_khost)
    (prop_host id_stimedelta id_rhost)
    (prop_host id_ztimedelta id_yhost)
    (PROP_HOSTNAME id_bfhost str__bj)
    (PROP_HOSTNAME id_bmhost str__bq)
    (PROP_HOSTNAME id_bthost str__bx)
    (PROP_HOSTNAME id_khost str__o)
    (PROP_HOSTNAME id_rhost str__v)
    (PROP_HOSTNAME id_yhost str__bc)
    (PROP_IS_GROUP id_cdomainuser no)
    (PROP_IS_GROUP id_gdomainuser no)
    (PROP_MICROSECONDS id_bgtimedelta num__34)
    (PROP_MICROSECONDS id_bntimedelta num__41)
    (PROP_MICROSECONDS id_butimedelta num__48)
    (PROP_MICROSECONDS id_ltimedelta num__13)
    (PROP_MICROSECONDS id_stimedelta num__20)
    (PROP_MICROSECONDS id_ztimedelta num__27)
    (PROP_PASSWORD id_ddomaincredential str__e)
    (PROP_PASSWORD id_hdomaincredential str__i)
    (PROP_SECONDS id_bgtimedelta num__33)
    (PROP_SECONDS id_bntimedelta num__40)
    (PROP_SECONDS id_butimedelta num__47)
    (PROP_SECONDS id_ltimedelta num__12)
    (PROP_SECONDS id_stimedelta num__19)
    (PROP_SECONDS id_ztimedelta num__26)
    (PROP_SID id_cdomainuser str__f)
    (PROP_SID id_gdomainuser str__j)
    (PROP_TIMEDELTA id_bfhost id_bgtimedelta)
    (PROP_TIMEDELTA id_bmhost id_bntimedelta)
    (PROP_TIMEDELTA id_bthost id_butimedelta)
    (PROP_TIMEDELTA id_khost id_ltimedelta)
    (PROP_TIMEDELTA id_rhost id_stimedelta)
    (PROP_TIMEDELTA id_yhost id_ztimedelta)
    (PROP_USER id_ddomaincredential id_cdomainuser)
    (PROP_USER id_hdomaincredential id_gdomainuser)
    (PROP_USERNAME id_cdomainuser str__james)
    (PROP_USERNAME id_gdomainuser str__mary)
    (PROP_WINDOWS_DOMAIN id_adomain str__alpha)
)
(:goal
(and
    (prop_host id_chrat id_yhost)
    (prop_host id_ccrat id_rhost)
    (prop_host id_cerat id_khost)
    (prop_host id_cdrat id_bthost)
    (prop_host id_cgrat id_bmhost)
)
)
)