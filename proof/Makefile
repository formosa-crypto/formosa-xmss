# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
ECRUNTEST  ?= $(EASYCRYPT) runtest
EC_FLAGS   ?= -timeout 20 ${ECADDFLAGS}

JASMIN2EC        ?= jasmin2ec
JASMIN2EC_FLAGS  ?= --array-model=old
JPATH            := JASMINPATH="XMSS=../ref-jasmin:Stdlib=../ref-jasmin/stdlib"

# --------------------------------------------------------------------------------------------------

default: extract check_spec check_proofs check_extraction
all: clean distclean extract check_spec check_proofs check_extraction
extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------------------------------------

.PHONY: check_spec check_proofs check_extraction check_xmss_spec check_xmss_mt_spec \
        check_correctness_proof check_security_proof check_xmss_xmssmt_proof

# --------------------------------------------------------------------------------------------------

common/Array8.ec: | common/
	printf "from Jasmin require import JArray.\n\nclone export PolyArray as Array8  with op size <- 8.\n" > $@

extraction/XMSS_IMPL.ec: ../ref-jasmin/xmss/xmss.jinc | common/
	printf "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > tmp
	cat $< >> tmp
	$(JPATH) $(JASMIN2EC) $(JASMIN2EC_FLAGS) tmp -o $@
	-$(RM) tmp
	mv extraction/WArray* common/
	mv extraction/Array* common/

# --------------------------------------------------------------------------------------------------

check_xmss_common_spec: common/Array8.ec
	$(ECRUNTEST) config/tests.config common-spec

check_xmss_spec: common/Array8.ec
	$(ECRUNTEST) config/tests.config xmss-spec

check_xmss_mt_spec: common/Array8.ec
	$(ECRUNTEST) config/tests.config xmss-mt-spec

# FIXME: This is currently not checked
check_xmss_spec_extra: common/Array8.ec
	$(ECRUNTEST) config/tests.config xmss-spec-extra

check_spec: common/Array8.ec check_xmss_common_spec check_xmss_spec check_xmss_mt_spec

check_extraction: extraction/XMSS_IMPL.ec
	$(ECRUNTEST) config/tests.config extraction

################################### correctness proof ##############################################

check_correctness_proof: extraction/XMSS_IMPL.ec
	$(ECRUNTEST) config/tests.config correctness

####################################################################################################

# FIXME: Only one of these is needed
check_security_proof:
	$(ECRUNTEST) config/tests.config xmss-acai
	$(ECRUNTEST) config/tests.config xmss-fsai

####################################################################################################

# FIXME: This would currently be subsumed by the xmss-spec-extra target, if activated
check_xmss_xmssmt_proof: common/Array8.ec
	$(EASYCRYPT) $(EC_FLAGS) spec/extra/XMSS_vs_XMSS_MT.ec

check_proofs: check_xmss_xmssmt_proof check_correctness_proof check_security_proof

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	-$(RM) -r *.eco
	-$(RM) -r *~ 
	-$(RM) -r \#*\#
	-$(RM) -r spec/xmss/*.eco
	-$(RM) -r spec/xmss/*~ 
	-$(RM) -r spec/xmss/\#*\#
	-$(RM) -r spec/xmss_mt/*.eco
	-$(RM) -r spec/xmss_mt/*~ 
	-$(RM) -r spec/xmss_mt/\#*\#
	-$(RM) -r correctness/*.eco
	-$(RM) -r correctness/*~ 
	-$(RM) -r correctness/\#*\#
	-$(RM) -r security/*/*.eco


.PHONY: distclean
distclean:
	-$(RM) -r extraction/XMSS_IMPL.ec common/

# --------------------------------------------------------------------------------------------------

extraction/:
	mkdir -p $@


common/:
	mkdir -p $@
