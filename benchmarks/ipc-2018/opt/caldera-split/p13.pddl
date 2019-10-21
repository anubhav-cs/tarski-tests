(define (problem p5_hosts_trial_1)
(:domain caldera-split)
(:objects
    id_adomain - observeddomain
    id_ddomaincredential - observeddomaincredential
    id_cdomainuser - observeddomainuser
    id_bihost - observedhost
    id_bbhost - observedhost
    id_uhost - observedhost
    id_nhost - observedhost
    id_ghost - observedhost
    num__15 - num
    num__8 - num
    num__23 - num
    num__9 - num
    num__37 - num
    num__29 - num
    num__30 - num
    num__36 - num
    num__16 - num
    num__22 - num
    id_byshare - observedshare
    id_bxshare - observedshare
    id_cashare - observedshare
    id_bwshare - observedshare
    id_bzshare - observedshare
    id_btschtask - observedschtask
    id_bsschtask - observedschtask
    id_brschtask - observedschtask
    id_buschtask - observedschtask
    id_bvschtask - observedschtask
    id_bctimedelta - observedtimedelta
    id_otimedelta - observedtimedelta
    id_bjtimedelta - observedtimedelta
    id_vtimedelta - observedtimedelta
    id_htimedelta - observedtimedelta
    id_ccfile - observedfile
    id_cffile - observedfile
    id_cefile - observedfile
    id_cdfile - observedfile
    id_cbfile - observedfile
    str__k - string
    str__bh - string
    str__bq - string
    str__r - string
    str__t - string
    str__bf - string
    str__ba - string
    str__m - string
    str__alpha - string
    str__z - string
    str__bo - string
    str__bm - string
    str__l - string
    str__s - string
    str__y - string
    str__bg - string
    str__bn - string
    str__james - string
    str__e - string
    str__f - string
    str__b - string
    id_cgrat - observedrat
    id_chrat - observedrat
    id_cirat - observedrat
    id_ckrat - observedrat
    id_cjrat - observedrat
    id_bprat - observedrat
)
(:init
    (knows id_bprat)
    (knows id_nhost)
    (knows_property id_bprat pexecutable)
    (knows_property id_bprat phost)
    (knows_property id_nhost pfqdn)
    (MEM_CACHED_DOMAIN_CREDS id_bbhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_bihost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ghost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_nhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_uhost id_ddomaincredential)
    (MEM_DOMAIN_USER_ADMINS id_bbhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_bihost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ghost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_nhost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_uhost id_cdomainuser)
    (mem_hosts id_adomain id_bbhost)
    (mem_hosts id_adomain id_bihost)
    (mem_hosts id_adomain id_ghost)
    (mem_hosts id_adomain id_nhost)
    (mem_hosts id_adomain id_uhost)
    (prop_cred id_cdomainuser id_ddomaincredential)
    (PROP_DC id_bbhost no)
    (PROP_DC id_bihost no)
    (PROP_DC id_ghost no)
    (PROP_DC id_nhost no)
    (PROP_DC id_uhost no)
    (PROP_DNS_DOMAIN id_adomain str__b)
    (PROP_DNS_DOMAIN_NAME id_bbhost str__bf)
    (PROP_DNS_DOMAIN_NAME id_bihost str__bm)
    (PROP_DNS_DOMAIN_NAME id_ghost str__k)
    (PROP_DNS_DOMAIN_NAME id_nhost str__r)
    (PROP_DNS_DOMAIN_NAME id_uhost str__y)
    (PROP_DOMAIN id_bbhost id_adomain)
    (PROP_DOMAIN id_bihost id_adomain)
    (PROP_DOMAIN id_cdomainuser id_adomain)
    (PROP_DOMAIN id_ddomaincredential id_adomain)
    (PROP_DOMAIN id_ghost id_adomain)
    (PROP_DOMAIN id_nhost id_adomain)
    (PROP_DOMAIN id_uhost id_adomain)
    (prop_elevated id_bprat yes)
    (prop_executable id_bprat str__bq)
    (PROP_FQDN id_bbhost str__bg)
    (PROP_FQDN id_bihost str__bn)
    (PROP_FQDN id_ghost str__l)
    (PROP_FQDN id_nhost str__s)
    (PROP_FQDN id_uhost str__z)
    (prop_host id_bctimedelta id_bbhost)
    (prop_host id_bjtimedelta id_bihost)
    (prop_host id_bprat id_nhost)
    (prop_host id_htimedelta id_ghost)
    (prop_host id_otimedelta id_nhost)
    (prop_host id_vtimedelta id_uhost)
    (PROP_HOSTNAME id_bbhost str__bh)
    (PROP_HOSTNAME id_bihost str__bo)
    (PROP_HOSTNAME id_ghost str__m)
    (PROP_HOSTNAME id_nhost str__t)
    (PROP_HOSTNAME id_uhost str__ba)
    (PROP_IS_GROUP id_cdomainuser no)
    (PROP_MICROSECONDS id_bctimedelta num__30)
    (PROP_MICROSECONDS id_bjtimedelta num__37)
    (PROP_MICROSECONDS id_htimedelta num__9)
    (PROP_MICROSECONDS id_otimedelta num__16)
    (PROP_MICROSECONDS id_vtimedelta num__23)
    (PROP_PASSWORD id_ddomaincredential str__e)
    (PROP_SECONDS id_bctimedelta num__29)
    (PROP_SECONDS id_bjtimedelta num__36)
    (PROP_SECONDS id_htimedelta num__8)
    (PROP_SECONDS id_otimedelta num__15)
    (PROP_SECONDS id_vtimedelta num__22)
    (PROP_SID id_cdomainuser str__f)
    (PROP_TIMEDELTA id_bbhost id_bctimedelta)
    (PROP_TIMEDELTA id_bihost id_bjtimedelta)
    (PROP_TIMEDELTA id_ghost id_htimedelta)
    (PROP_TIMEDELTA id_nhost id_otimedelta)
    (PROP_TIMEDELTA id_uhost id_vtimedelta)
    (PROP_USER id_ddomaincredential id_cdomainuser)
    (PROP_USERNAME id_cdomainuser str__james)
    (PROP_WINDOWS_DOMAIN id_adomain str__alpha)
    (procnone)
    (= (total-cost) 0)
)
(:goal
(and
    (procnone)
    (prop_host id_chrat id_uhost)
    (prop_host id_cgrat id_bbhost)
    (prop_host id_cjrat id_bihost)
    (prop_host id_ckrat id_ghost)
)
)
(:metric minimize (total-cost))
)