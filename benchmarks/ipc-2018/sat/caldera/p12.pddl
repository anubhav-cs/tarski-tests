;Copyright 2018 The MITRE Corporation. All rights reserved. Approved for public release. Distribution unlimited 17-2122.
; For more information on CALDERA, the automated adversary emulation system, visit https://github.com/mitre/caldera or email attack@mitre.org
; This has 8 hosts, 48 user, 5 admin per host, 4 active account per host
(define (problem p8_hosts_trial_8)
(:domain caldera)
(:objects
    num__238 num__211 num__231 num__203 num__239 num__232 num__196 num__217 num__204 num__197 num__218 num__224 num__225 num__245 num__246 num__210 - num
    id_cgdomainuser id_fedomainuser id_wdomainuser id_ckdomainuser id_hidomainuser id_bedomainuser id_fmdomainuser id_dydomainuser id_bidomainuser id_dudomainuser id_fydomainuser id_bmdomainuser id_hadomainuser id_dqdomainuser id_esdomainuser id_eodomainuser id_odomainuser id_dmdomainuser id_fudomainuser id_sdomainuser id_codomainuser id_fqdomainuser id_godomainuser id_gwdomainuser id_ggdomainuser id_kdomainuser id_gcdomainuser id_budomainuser id_cdomainuser id_gsdomainuser id_fadomainuser id_csdomainuser id_fidomainuser id_bydomainuser id_badomainuser id_gdomainuser id_gkdomainuser id_ewdomainuser id_hedomainuser id_egdomainuser id_cwdomainuser id_didomainuser id_ekdomainuser id_bqdomainuser id_dedomainuser id_ecdomainuser id_ccdomainuser id_dadomainuser - observeddomainuser
    id_jdtimedelta id_iitimedelta id_iptimedelta id_hutimedelta id_ibtimedelta id_jktimedelta id_iwtimedelta id_hntimedelta - observedtimedelta
    id_iahost id_jjhost id_jchost id_ivhost id_hthost id_ihhost id_iohost id_hmhost - observedhost
    id_gpdomaincredential id_bbdomaincredential id_ctdomaincredential id_fndomaincredential id_gldomaincredential id_cldomaincredential id_ddomaincredential id_dvdomaincredential id_dzdomaincredential id_eldomaincredential id_epdomaincredential id_pdomaincredential id_frdomaincredential id_xdomaincredential id_gxdomaincredential id_dbdomaincredential id_gtdomaincredential id_drdomaincredential id_bjdomaincredential id_tdomaincredential id_fbdomaincredential id_cddomaincredential id_ffdomaincredential id_ldomaincredential id_ehdomaincredential id_brdomaincredential id_djdomaincredential id_hfdomaincredential id_hjdomaincredential id_cxdomaincredential id_dndomaincredential id_eddomaincredential id_fvdomaincredential id_bzdomaincredential id_hbdomaincredential id_chdomaincredential id_fzdomaincredential id_bndomaincredential id_bvdomaincredential id_cpdomaincredential id_dfdomaincredential id_bfdomaincredential id_gddomaincredential id_etdomaincredential id_ghdomaincredential id_fjdomaincredential id_hdomaincredential id_exdomaincredential - observeddomaincredential
    str__jennifer str__hz str__sandra str__hl str__ce str__cm str__ja str__cn str__nancy str__christopher str__bx str__is str__ef str__dl str__edward str__dt str__helen str__fl str__ei str__steven str__ej str__margaret str__barbara str__it str__ie str__ruth str__bl str__david str__dg str__ee str__ci str__jo str__george str__gz str__hh str__robert str__dd str__ev str__gn str__fk str__anthony str__dc str__fo str__gj str__ge str__kimberly str__eu str__jason str__im str__fs str__carol str__dk str__hd str__cr str__i str__ft str__james str__dh str__patricia str__gr str__hc str__eb str__u str__thomas str__hq str__dp str__b str__jr str__joseph str__jp str__n str__elizabeth str__q str__gb str__hx str__gq str__iz str__hs str__fg str__kevin str__alpha str__ig str__john str__gm str__ez str__laura str__kenneth str__bo str__gy str__iu str__if str__donald str__cb str__karen str__fc str__donna str__mary str__cj str__bd str__em str__fw str__gi str__sharon str__fp str__dorothy str__betty str__cz str__v str__ea str__e str__in str__ds str__fd str__ey str__hg str__cu str__cq str__hr str__bp str__fh str__bw str__ca str__jh str__cf str__gu str__eq str__linda str__paul str__jb str__y str__hy str__fx str__dx str__jn str__charles str__ji str__bg str__daniel str__brian str__r str__do str__dw str__m str__hk str__richard str__gv str__bs str__cy str__sarah str__bk str__cv str__gf str__z str__susan str__michael str__en str__ronald str__bc str__mark str__ga str__bh str__j str__william str__f str__jg str__maria str__er str__lisa str__il str__michelle str__bt - string
    id_adomain - observeddomain
    id_jqrat id_jxrat id_jvrat id_jsrat id_jurat id_jwrat id_jtrat id_jyrat id_jzrat - observedrat
    id_kcschtask id_kfschtask id_kbschtask id_kgschtask id_khschtask id_kaschtask id_kdschtask id_keschtask - observedschtask
    id_ktshare id_ksshare id_kqshare id_kvshare id_kushare id_kxshare id_kwshare id_krshare - observedshare
    id_knfile id_kmfile id_kkfile id_kifile id_kjfile id_kofile id_kpfile id_klfile - observedfile
)
(:init
    (knows id_hthost)
    (knows id_jqrat)
    (knows_property id_hthost pfqdn)
    (knows_property id_jqrat pexecutable)
    (knows_property id_jqrat phost)
    (MEM_CACHED_DOMAIN_CREDS id_hmhost id_cpdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_hmhost id_dzdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_hmhost id_gpdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_hmhost id_hfdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_hthost id_bjdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_hthost id_dzdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_hthost id_eddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_hthost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iahost id_cddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iahost id_dfdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iahost id_fvdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iahost id_hfdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ihhost id_ddomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ihhost id_exdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ihhost id_fvdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ihhost id_pdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iohost id_cldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iohost id_cpdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iohost id_dvdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_iohost id_eldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ivhost id_cxdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ivhost id_fndomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ivhost id_gtdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_ivhost id_hbdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jchost id_cldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jchost id_drdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jchost id_dzdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jchost id_exdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jjhost id_cxdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jjhost id_dbdomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jjhost id_gldomaincredential)
    (MEM_CACHED_DOMAIN_CREDS id_jjhost id_pdomaincredential)
    (MEM_DOMAIN_USER_ADMINS id_hmhost id_cwdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hmhost id_dedomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hmhost id_ecdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hmhost id_gwdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hmhost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hthost id_csdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hthost id_dydomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hthost id_fadomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hthost id_fqdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_hthost id_hadomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iahost id_bedomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iahost id_fydomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iahost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iahost id_odomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iahost id_wdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ihhost id_bidomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ihhost id_cwdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ihhost id_dudomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ihhost id_fqdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ihhost id_wdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iohost id_badomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iohost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iohost id_codomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iohost id_dedomainuser)
    (MEM_DOMAIN_USER_ADMINS id_iohost id_didomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ivhost id_bedomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ivhost id_codomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ivhost id_dmdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ivhost id_gsdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_ivhost id_hidomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jchost id_cdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jchost id_codomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jchost id_csdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jchost id_kdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jchost id_odomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jjhost id_bmdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jjhost id_bydomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jjhost id_codomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jjhost id_ewdomainuser)
    (MEM_DOMAIN_USER_ADMINS id_jjhost id_kdomainuser)
    (mem_hosts id_adomain id_hmhost)
    (mem_hosts id_adomain id_hthost)
    (mem_hosts id_adomain id_iahost)
    (mem_hosts id_adomain id_ihhost)
    (mem_hosts id_adomain id_iohost)
    (mem_hosts id_adomain id_ivhost)
    (mem_hosts id_adomain id_jchost)
    (mem_hosts id_adomain id_jjhost)
    (prop_cred id_badomainuser id_bbdomaincredential)
    (prop_cred id_bedomainuser id_bfdomaincredential)
    (prop_cred id_bidomainuser id_bjdomaincredential)
    (prop_cred id_bmdomainuser id_bndomaincredential)
    (prop_cred id_bqdomainuser id_brdomaincredential)
    (prop_cred id_budomainuser id_bvdomaincredential)
    (prop_cred id_bydomainuser id_bzdomaincredential)
    (prop_cred id_cdomainuser id_ddomaincredential)
    (prop_cred id_ccdomainuser id_cddomaincredential)
    (prop_cred id_cgdomainuser id_chdomaincredential)
    (prop_cred id_ckdomainuser id_cldomaincredential)
    (prop_cred id_codomainuser id_cpdomaincredential)
    (prop_cred id_csdomainuser id_ctdomaincredential)
    (prop_cred id_cwdomainuser id_cxdomaincredential)
    (prop_cred id_dadomainuser id_dbdomaincredential)
    (prop_cred id_dedomainuser id_dfdomaincredential)
    (prop_cred id_didomainuser id_djdomaincredential)
    (prop_cred id_dmdomainuser id_dndomaincredential)
    (prop_cred id_dqdomainuser id_drdomaincredential)
    (prop_cred id_dudomainuser id_dvdomaincredential)
    (prop_cred id_dydomainuser id_dzdomaincredential)
    (prop_cred id_ecdomainuser id_eddomaincredential)
    (prop_cred id_egdomainuser id_ehdomaincredential)
    (prop_cred id_ekdomainuser id_eldomaincredential)
    (prop_cred id_eodomainuser id_epdomaincredential)
    (prop_cred id_esdomainuser id_etdomaincredential)
    (prop_cred id_ewdomainuser id_exdomaincredential)
    (prop_cred id_fadomainuser id_fbdomaincredential)
    (prop_cred id_fedomainuser id_ffdomaincredential)
    (prop_cred id_fidomainuser id_fjdomaincredential)
    (prop_cred id_fmdomainuser id_fndomaincredential)
    (prop_cred id_fqdomainuser id_frdomaincredential)
    (prop_cred id_fudomainuser id_fvdomaincredential)
    (prop_cred id_fydomainuser id_fzdomaincredential)
    (prop_cred id_gdomainuser id_hdomaincredential)
    (prop_cred id_gcdomainuser id_gddomaincredential)
    (prop_cred id_ggdomainuser id_ghdomaincredential)
    (prop_cred id_gkdomainuser id_gldomaincredential)
    (prop_cred id_godomainuser id_gpdomaincredential)
    (prop_cred id_gsdomainuser id_gtdomaincredential)
    (prop_cred id_gwdomainuser id_gxdomaincredential)
    (prop_cred id_hadomainuser id_hbdomaincredential)
    (prop_cred id_hedomainuser id_hfdomaincredential)
    (prop_cred id_hidomainuser id_hjdomaincredential)
    (prop_cred id_kdomainuser id_ldomaincredential)
    (prop_cred id_odomainuser id_pdomaincredential)
    (prop_cred id_sdomainuser id_tdomaincredential)
    (prop_cred id_wdomainuser id_xdomaincredential)
    (PROP_DC id_hmhost yes)
    (PROP_DC id_hthost yes)
    (PROP_DC id_iahost no)
    (PROP_DC id_ihhost no)
    (PROP_DC id_iohost no)
    (PROP_DC id_ivhost no)
    (PROP_DC id_jchost no)
    (PROP_DC id_jjhost no)
    (PROP_DNS_DOMAIN id_adomain str__b)
    (PROP_DNS_DOMAIN_NAME id_hmhost str__hr)
    (PROP_DNS_DOMAIN_NAME id_hthost str__hy)
    (PROP_DNS_DOMAIN_NAME id_iahost str__if)
    (PROP_DNS_DOMAIN_NAME id_ihhost str__im)
    (PROP_DNS_DOMAIN_NAME id_iohost str__it)
    (PROP_DNS_DOMAIN_NAME id_ivhost str__ja)
    (PROP_DNS_DOMAIN_NAME id_jchost str__jh)
    (PROP_DNS_DOMAIN_NAME id_jjhost str__jo)
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
    (PROP_DOMAIN id_bydomainuser id_adomain)
    (PROP_DOMAIN id_bzdomaincredential id_adomain)
    (PROP_DOMAIN id_cdomainuser id_adomain)
    (PROP_DOMAIN id_ccdomainuser id_adomain)
    (PROP_DOMAIN id_cddomaincredential id_adomain)
    (PROP_DOMAIN id_cgdomainuser id_adomain)
    (PROP_DOMAIN id_chdomaincredential id_adomain)
    (PROP_DOMAIN id_ckdomainuser id_adomain)
    (PROP_DOMAIN id_cldomaincredential id_adomain)
    (PROP_DOMAIN id_codomainuser id_adomain)
    (PROP_DOMAIN id_cpdomaincredential id_adomain)
    (PROP_DOMAIN id_csdomainuser id_adomain)
    (PROP_DOMAIN id_ctdomaincredential id_adomain)
    (PROP_DOMAIN id_cwdomainuser id_adomain)
    (PROP_DOMAIN id_cxdomaincredential id_adomain)
    (PROP_DOMAIN id_ddomaincredential id_adomain)
    (PROP_DOMAIN id_dadomainuser id_adomain)
    (PROP_DOMAIN id_dbdomaincredential id_adomain)
    (PROP_DOMAIN id_dedomainuser id_adomain)
    (PROP_DOMAIN id_dfdomaincredential id_adomain)
    (PROP_DOMAIN id_didomainuser id_adomain)
    (PROP_DOMAIN id_djdomaincredential id_adomain)
    (PROP_DOMAIN id_dmdomainuser id_adomain)
    (PROP_DOMAIN id_dndomaincredential id_adomain)
    (PROP_DOMAIN id_dqdomainuser id_adomain)
    (PROP_DOMAIN id_drdomaincredential id_adomain)
    (PROP_DOMAIN id_dudomainuser id_adomain)
    (PROP_DOMAIN id_dvdomaincredential id_adomain)
    (PROP_DOMAIN id_dydomainuser id_adomain)
    (PROP_DOMAIN id_dzdomaincredential id_adomain)
    (PROP_DOMAIN id_ecdomainuser id_adomain)
    (PROP_DOMAIN id_eddomaincredential id_adomain)
    (PROP_DOMAIN id_egdomainuser id_adomain)
    (PROP_DOMAIN id_ehdomaincredential id_adomain)
    (PROP_DOMAIN id_ekdomainuser id_adomain)
    (PROP_DOMAIN id_eldomaincredential id_adomain)
    (PROP_DOMAIN id_eodomainuser id_adomain)
    (PROP_DOMAIN id_epdomaincredential id_adomain)
    (PROP_DOMAIN id_esdomainuser id_adomain)
    (PROP_DOMAIN id_etdomaincredential id_adomain)
    (PROP_DOMAIN id_ewdomainuser id_adomain)
    (PROP_DOMAIN id_exdomaincredential id_adomain)
    (PROP_DOMAIN id_fadomainuser id_adomain)
    (PROP_DOMAIN id_fbdomaincredential id_adomain)
    (PROP_DOMAIN id_fedomainuser id_adomain)
    (PROP_DOMAIN id_ffdomaincredential id_adomain)
    (PROP_DOMAIN id_fidomainuser id_adomain)
    (PROP_DOMAIN id_fjdomaincredential id_adomain)
    (PROP_DOMAIN id_fmdomainuser id_adomain)
    (PROP_DOMAIN id_fndomaincredential id_adomain)
    (PROP_DOMAIN id_fqdomainuser id_adomain)
    (PROP_DOMAIN id_frdomaincredential id_adomain)
    (PROP_DOMAIN id_fudomainuser id_adomain)
    (PROP_DOMAIN id_fvdomaincredential id_adomain)
    (PROP_DOMAIN id_fydomainuser id_adomain)
    (PROP_DOMAIN id_fzdomaincredential id_adomain)
    (PROP_DOMAIN id_gdomainuser id_adomain)
    (PROP_DOMAIN id_gcdomainuser id_adomain)
    (PROP_DOMAIN id_gddomaincredential id_adomain)
    (PROP_DOMAIN id_ggdomainuser id_adomain)
    (PROP_DOMAIN id_ghdomaincredential id_adomain)
    (PROP_DOMAIN id_gkdomainuser id_adomain)
    (PROP_DOMAIN id_gldomaincredential id_adomain)
    (PROP_DOMAIN id_godomainuser id_adomain)
    (PROP_DOMAIN id_gpdomaincredential id_adomain)
    (PROP_DOMAIN id_gsdomainuser id_adomain)
    (PROP_DOMAIN id_gtdomaincredential id_adomain)
    (PROP_DOMAIN id_gwdomainuser id_adomain)
    (PROP_DOMAIN id_gxdomaincredential id_adomain)
    (PROP_DOMAIN id_hdomaincredential id_adomain)
    (PROP_DOMAIN id_hadomainuser id_adomain)
    (PROP_DOMAIN id_hbdomaincredential id_adomain)
    (PROP_DOMAIN id_hedomainuser id_adomain)
    (PROP_DOMAIN id_hfdomaincredential id_adomain)
    (PROP_DOMAIN id_hidomainuser id_adomain)
    (PROP_DOMAIN id_hjdomaincredential id_adomain)
    (PROP_DOMAIN id_hmhost id_adomain)
    (PROP_DOMAIN id_hthost id_adomain)
    (PROP_DOMAIN id_iahost id_adomain)
    (PROP_DOMAIN id_ihhost id_adomain)
    (PROP_DOMAIN id_iohost id_adomain)
    (PROP_DOMAIN id_ivhost id_adomain)
    (PROP_DOMAIN id_jchost id_adomain)
    (PROP_DOMAIN id_jjhost id_adomain)
    (PROP_DOMAIN id_kdomainuser id_adomain)
    (PROP_DOMAIN id_ldomaincredential id_adomain)
    (PROP_DOMAIN id_odomainuser id_adomain)
    (PROP_DOMAIN id_pdomaincredential id_adomain)
    (PROP_DOMAIN id_sdomainuser id_adomain)
    (PROP_DOMAIN id_tdomaincredential id_adomain)
    (PROP_DOMAIN id_wdomainuser id_adomain)
    (PROP_DOMAIN id_xdomaincredential id_adomain)
    (prop_elevated id_jqrat yes)
    (prop_executable id_jqrat str__jr)
    (PROP_FQDN id_hmhost str__hs)
    (PROP_FQDN id_hthost str__hz)
    (PROP_FQDN id_iahost str__ig)
    (PROP_FQDN id_ihhost str__in)
    (PROP_FQDN id_iohost str__iu)
    (PROP_FQDN id_ivhost str__jb)
    (PROP_FQDN id_jchost str__ji)
    (PROP_FQDN id_jjhost str__jp)
    (prop_host id_hntimedelta id_hmhost)
    (prop_host id_hutimedelta id_hthost)
    (prop_host id_ibtimedelta id_iahost)
    (prop_host id_iitimedelta id_ihhost)
    (prop_host id_iptimedelta id_iohost)
    (prop_host id_iwtimedelta id_ivhost)
    (prop_host id_jdtimedelta id_jchost)
    (prop_host id_jktimedelta id_jjhost)
    (prop_host id_jqrat id_hthost)
    (PROP_HOSTNAME id_hmhost str__hq)
    (PROP_HOSTNAME id_hthost str__hx)
    (PROP_HOSTNAME id_iahost str__ie)
    (PROP_HOSTNAME id_ihhost str__il)
    (PROP_HOSTNAME id_iohost str__is)
    (PROP_HOSTNAME id_ivhost str__iz)
    (PROP_HOSTNAME id_jchost str__jg)
    (PROP_HOSTNAME id_jjhost str__jn)
    (PROP_IS_GROUP id_badomainuser no)
    (PROP_IS_GROUP id_bedomainuser no)
    (PROP_IS_GROUP id_bidomainuser no)
    (PROP_IS_GROUP id_bmdomainuser no)
    (PROP_IS_GROUP id_bqdomainuser no)
    (PROP_IS_GROUP id_budomainuser no)
    (PROP_IS_GROUP id_bydomainuser no)
    (PROP_IS_GROUP id_cdomainuser no)
    (PROP_IS_GROUP id_ccdomainuser no)
    (PROP_IS_GROUP id_cgdomainuser no)
    (PROP_IS_GROUP id_ckdomainuser no)
    (PROP_IS_GROUP id_codomainuser no)
    (PROP_IS_GROUP id_csdomainuser no)
    (PROP_IS_GROUP id_cwdomainuser no)
    (PROP_IS_GROUP id_dadomainuser no)
    (PROP_IS_GROUP id_dedomainuser no)
    (PROP_IS_GROUP id_didomainuser no)
    (PROP_IS_GROUP id_dmdomainuser no)
    (PROP_IS_GROUP id_dqdomainuser no)
    (PROP_IS_GROUP id_dudomainuser no)
    (PROP_IS_GROUP id_dydomainuser no)
    (PROP_IS_GROUP id_ecdomainuser no)
    (PROP_IS_GROUP id_egdomainuser no)
    (PROP_IS_GROUP id_ekdomainuser no)
    (PROP_IS_GROUP id_eodomainuser no)
    (PROP_IS_GROUP id_esdomainuser no)
    (PROP_IS_GROUP id_ewdomainuser no)
    (PROP_IS_GROUP id_fadomainuser no)
    (PROP_IS_GROUP id_fedomainuser no)
    (PROP_IS_GROUP id_fidomainuser no)
    (PROP_IS_GROUP id_fmdomainuser no)
    (PROP_IS_GROUP id_fqdomainuser no)
    (PROP_IS_GROUP id_fudomainuser no)
    (PROP_IS_GROUP id_fydomainuser no)
    (PROP_IS_GROUP id_gdomainuser no)
    (PROP_IS_GROUP id_gcdomainuser no)
    (PROP_IS_GROUP id_ggdomainuser no)
    (PROP_IS_GROUP id_gkdomainuser no)
    (PROP_IS_GROUP id_godomainuser no)
    (PROP_IS_GROUP id_gsdomainuser no)
    (PROP_IS_GROUP id_gwdomainuser no)
    (PROP_IS_GROUP id_hadomainuser no)
    (PROP_IS_GROUP id_hedomainuser no)
    (PROP_IS_GROUP id_hidomainuser no)
    (PROP_IS_GROUP id_kdomainuser no)
    (PROP_IS_GROUP id_odomainuser no)
    (PROP_IS_GROUP id_sdomainuser no)
    (PROP_IS_GROUP id_wdomainuser no)
    (PROP_MICROSECONDS id_hntimedelta num__196)
    (PROP_MICROSECONDS id_hutimedelta num__203)
    (PROP_MICROSECONDS id_ibtimedelta num__210)
    (PROP_MICROSECONDS id_iitimedelta num__217)
    (PROP_MICROSECONDS id_iptimedelta num__224)
    (PROP_MICROSECONDS id_iwtimedelta num__231)
    (PROP_MICROSECONDS id_jdtimedelta num__238)
    (PROP_MICROSECONDS id_jktimedelta num__245)
    (PROP_PASSWORD id_bbdomaincredential str__bc)
    (PROP_PASSWORD id_bfdomaincredential str__bg)
    (PROP_PASSWORD id_bjdomaincredential str__bk)
    (PROP_PASSWORD id_bndomaincredential str__bo)
    (PROP_PASSWORD id_brdomaincredential str__bs)
    (PROP_PASSWORD id_bvdomaincredential str__bw)
    (PROP_PASSWORD id_bzdomaincredential str__ca)
    (PROP_PASSWORD id_cddomaincredential str__ce)
    (PROP_PASSWORD id_chdomaincredential str__ci)
    (PROP_PASSWORD id_cldomaincredential str__cm)
    (PROP_PASSWORD id_cpdomaincredential str__cq)
    (PROP_PASSWORD id_ctdomaincredential str__cu)
    (PROP_PASSWORD id_cxdomaincredential str__cy)
    (PROP_PASSWORD id_ddomaincredential str__e)
    (PROP_PASSWORD id_dbdomaincredential str__dc)
    (PROP_PASSWORD id_dfdomaincredential str__dg)
    (PROP_PASSWORD id_djdomaincredential str__dk)
    (PROP_PASSWORD id_dndomaincredential str__do)
    (PROP_PASSWORD id_drdomaincredential str__ds)
    (PROP_PASSWORD id_dvdomaincredential str__dw)
    (PROP_PASSWORD id_dzdomaincredential str__ea)
    (PROP_PASSWORD id_eddomaincredential str__ee)
    (PROP_PASSWORD id_ehdomaincredential str__ei)
    (PROP_PASSWORD id_eldomaincredential str__em)
    (PROP_PASSWORD id_epdomaincredential str__eq)
    (PROP_PASSWORD id_etdomaincredential str__eu)
    (PROP_PASSWORD id_exdomaincredential str__ey)
    (PROP_PASSWORD id_fbdomaincredential str__fc)
    (PROP_PASSWORD id_ffdomaincredential str__fg)
    (PROP_PASSWORD id_fjdomaincredential str__fk)
    (PROP_PASSWORD id_fndomaincredential str__fo)
    (PROP_PASSWORD id_frdomaincredential str__fs)
    (PROP_PASSWORD id_fvdomaincredential str__fw)
    (PROP_PASSWORD id_fzdomaincredential str__ga)
    (PROP_PASSWORD id_gddomaincredential str__ge)
    (PROP_PASSWORD id_ghdomaincredential str__gi)
    (PROP_PASSWORD id_gldomaincredential str__gm)
    (PROP_PASSWORD id_gpdomaincredential str__gq)
    (PROP_PASSWORD id_gtdomaincredential str__gu)
    (PROP_PASSWORD id_gxdomaincredential str__gy)
    (PROP_PASSWORD id_hdomaincredential str__i)
    (PROP_PASSWORD id_hbdomaincredential str__hc)
    (PROP_PASSWORD id_hfdomaincredential str__hg)
    (PROP_PASSWORD id_hjdomaincredential str__hk)
    (PROP_PASSWORD id_ldomaincredential str__m)
    (PROP_PASSWORD id_pdomaincredential str__q)
    (PROP_PASSWORD id_tdomaincredential str__u)
    (PROP_PASSWORD id_xdomaincredential str__y)
    (PROP_SECONDS id_hntimedelta num__197)
    (PROP_SECONDS id_hutimedelta num__204)
    (PROP_SECONDS id_ibtimedelta num__211)
    (PROP_SECONDS id_iitimedelta num__218)
    (PROP_SECONDS id_iptimedelta num__225)
    (PROP_SECONDS id_iwtimedelta num__232)
    (PROP_SECONDS id_jdtimedelta num__239)
    (PROP_SECONDS id_jktimedelta num__246)
    (PROP_SID id_badomainuser str__bd)
    (PROP_SID id_bedomainuser str__bh)
    (PROP_SID id_bidomainuser str__bl)
    (PROP_SID id_bmdomainuser str__bp)
    (PROP_SID id_bqdomainuser str__bt)
    (PROP_SID id_budomainuser str__bx)
    (PROP_SID id_bydomainuser str__cb)
    (PROP_SID id_cdomainuser str__f)
    (PROP_SID id_ccdomainuser str__cf)
    (PROP_SID id_cgdomainuser str__cj)
    (PROP_SID id_ckdomainuser str__cn)
    (PROP_SID id_codomainuser str__cr)
    (PROP_SID id_csdomainuser str__cv)
    (PROP_SID id_cwdomainuser str__cz)
    (PROP_SID id_dadomainuser str__dd)
    (PROP_SID id_dedomainuser str__dh)
    (PROP_SID id_didomainuser str__dl)
    (PROP_SID id_dmdomainuser str__dp)
    (PROP_SID id_dqdomainuser str__dt)
    (PROP_SID id_dudomainuser str__dx)
    (PROP_SID id_dydomainuser str__eb)
    (PROP_SID id_ecdomainuser str__ef)
    (PROP_SID id_egdomainuser str__ej)
    (PROP_SID id_ekdomainuser str__en)
    (PROP_SID id_eodomainuser str__er)
    (PROP_SID id_esdomainuser str__ev)
    (PROP_SID id_ewdomainuser str__ez)
    (PROP_SID id_fadomainuser str__fd)
    (PROP_SID id_fedomainuser str__fh)
    (PROP_SID id_fidomainuser str__fl)
    (PROP_SID id_fmdomainuser str__fp)
    (PROP_SID id_fqdomainuser str__ft)
    (PROP_SID id_fudomainuser str__fx)
    (PROP_SID id_fydomainuser str__gb)
    (PROP_SID id_gdomainuser str__j)
    (PROP_SID id_gcdomainuser str__gf)
    (PROP_SID id_ggdomainuser str__gj)
    (PROP_SID id_gkdomainuser str__gn)
    (PROP_SID id_godomainuser str__gr)
    (PROP_SID id_gsdomainuser str__gv)
    (PROP_SID id_gwdomainuser str__gz)
    (PROP_SID id_hadomainuser str__hd)
    (PROP_SID id_hedomainuser str__hh)
    (PROP_SID id_hidomainuser str__hl)
    (PROP_SID id_kdomainuser str__n)
    (PROP_SID id_odomainuser str__r)
    (PROP_SID id_sdomainuser str__v)
    (PROP_SID id_wdomainuser str__z)
    (PROP_TIMEDELTA id_hmhost id_hntimedelta)
    (PROP_TIMEDELTA id_hthost id_hutimedelta)
    (PROP_TIMEDELTA id_iahost id_ibtimedelta)
    (PROP_TIMEDELTA id_ihhost id_iitimedelta)
    (PROP_TIMEDELTA id_iohost id_iptimedelta)
    (PROP_TIMEDELTA id_ivhost id_iwtimedelta)
    (PROP_TIMEDELTA id_jchost id_jdtimedelta)
    (PROP_TIMEDELTA id_jjhost id_jktimedelta)
    (PROP_USER id_bbdomaincredential id_badomainuser)
    (PROP_USER id_bfdomaincredential id_bedomainuser)
    (PROP_USER id_bjdomaincredential id_bidomainuser)
    (PROP_USER id_bndomaincredential id_bmdomainuser)
    (PROP_USER id_brdomaincredential id_bqdomainuser)
    (PROP_USER id_bvdomaincredential id_budomainuser)
    (PROP_USER id_bzdomaincredential id_bydomainuser)
    (PROP_USER id_cddomaincredential id_ccdomainuser)
    (PROP_USER id_chdomaincredential id_cgdomainuser)
    (PROP_USER id_cldomaincredential id_ckdomainuser)
    (PROP_USER id_cpdomaincredential id_codomainuser)
    (PROP_USER id_ctdomaincredential id_csdomainuser)
    (PROP_USER id_cxdomaincredential id_cwdomainuser)
    (PROP_USER id_ddomaincredential id_cdomainuser)
    (PROP_USER id_dbdomaincredential id_dadomainuser)
    (PROP_USER id_dfdomaincredential id_dedomainuser)
    (PROP_USER id_djdomaincredential id_didomainuser)
    (PROP_USER id_dndomaincredential id_dmdomainuser)
    (PROP_USER id_drdomaincredential id_dqdomainuser)
    (PROP_USER id_dvdomaincredential id_dudomainuser)
    (PROP_USER id_dzdomaincredential id_dydomainuser)
    (PROP_USER id_eddomaincredential id_ecdomainuser)
    (PROP_USER id_ehdomaincredential id_egdomainuser)
    (PROP_USER id_eldomaincredential id_ekdomainuser)
    (PROP_USER id_epdomaincredential id_eodomainuser)
    (PROP_USER id_etdomaincredential id_esdomainuser)
    (PROP_USER id_exdomaincredential id_ewdomainuser)
    (PROP_USER id_fbdomaincredential id_fadomainuser)
    (PROP_USER id_ffdomaincredential id_fedomainuser)
    (PROP_USER id_fjdomaincredential id_fidomainuser)
    (PROP_USER id_fndomaincredential id_fmdomainuser)
    (PROP_USER id_frdomaincredential id_fqdomainuser)
    (PROP_USER id_fvdomaincredential id_fudomainuser)
    (PROP_USER id_fzdomaincredential id_fydomainuser)
    (PROP_USER id_gddomaincredential id_gcdomainuser)
    (PROP_USER id_ghdomaincredential id_ggdomainuser)
    (PROP_USER id_gldomaincredential id_gkdomainuser)
    (PROP_USER id_gpdomaincredential id_godomainuser)
    (PROP_USER id_gtdomaincredential id_gsdomainuser)
    (PROP_USER id_gxdomaincredential id_gwdomainuser)
    (PROP_USER id_hdomaincredential id_gdomainuser)
    (PROP_USER id_hbdomaincredential id_hadomainuser)
    (PROP_USER id_hfdomaincredential id_hedomainuser)
    (PROP_USER id_hjdomaincredential id_hidomainuser)
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
    (PROP_USERNAME id_bydomainuser str__richard)
    (PROP_USERNAME id_cdomainuser str__james)
    (PROP_USERNAME id_ccdomainuser str__maria)
    (PROP_USERNAME id_cgdomainuser str__charles)
    (PROP_USERNAME id_ckdomainuser str__susan)
    (PROP_USERNAME id_codomainuser str__joseph)
    (PROP_USERNAME id_csdomainuser str__margaret)
    (PROP_USERNAME id_cwdomainuser str__thomas)
    (PROP_USERNAME id_dadomainuser str__dorothy)
    (PROP_USERNAME id_dedomainuser str__christopher)
    (PROP_USERNAME id_didomainuser str__lisa)
    (PROP_USERNAME id_dmdomainuser str__daniel)
    (PROP_USERNAME id_dqdomainuser str__nancy)
    (PROP_USERNAME id_dudomainuser str__paul)
    (PROP_USERNAME id_dydomainuser str__karen)
    (PROP_USERNAME id_ecdomainuser str__mark)
    (PROP_USERNAME id_egdomainuser str__betty)
    (PROP_USERNAME id_ekdomainuser str__donald)
    (PROP_USERNAME id_eodomainuser str__helen)
    (PROP_USERNAME id_esdomainuser str__george)
    (PROP_USERNAME id_ewdomainuser str__sandra)
    (PROP_USERNAME id_fadomainuser str__kenneth)
    (PROP_USERNAME id_fedomainuser str__donna)
    (PROP_USERNAME id_fidomainuser str__steven)
    (PROP_USERNAME id_fmdomainuser str__carol)
    (PROP_USERNAME id_fqdomainuser str__edward)
    (PROP_USERNAME id_fudomainuser str__ruth)
    (PROP_USERNAME id_fydomainuser str__brian)
    (PROP_USERNAME id_gdomainuser str__mary)
    (PROP_USERNAME id_gcdomainuser str__sharon)
    (PROP_USERNAME id_ggdomainuser str__ronald)
    (PROP_USERNAME id_gkdomainuser str__michelle)
    (PROP_USERNAME id_godomainuser str__anthony)
    (PROP_USERNAME id_gsdomainuser str__laura)
    (PROP_USERNAME id_gwdomainuser str__kevin)
    (PROP_USERNAME id_hadomainuser str__sarah)
    (PROP_USERNAME id_hedomainuser str__jason)
    (PROP_USERNAME id_hidomainuser str__kimberly)
    (PROP_USERNAME id_kdomainuser str__john)
    (PROP_USERNAME id_odomainuser str__patricia)
    (PROP_USERNAME id_sdomainuser str__robert)
    (PROP_USERNAME id_wdomainuser str__linda)
    (PROP_WINDOWS_DOMAIN id_adomain str__alpha)
)
(:goal
(and
    (prop_host id_jzrat id_hmhost)
    (prop_host id_jxrat id_iahost)
    (prop_host id_jvrat id_jjhost)
    (prop_host id_jsrat id_jchost)
    (prop_host id_jurat id_ivhost)
    (prop_host id_jwrat id_ihhost)
    (prop_host id_jtrat id_iohost)
)
)
)