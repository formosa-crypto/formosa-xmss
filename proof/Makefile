# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_FLAGS   ?= ${ECADDFLAGS}
ECRUNTEST  ?= $(EASYCRYPT) runtest $(EC_FLAGS) # So we can set the number of jobs (e.g. make check_correctness_proof EC_FLAGS='-jobs 4')

JASMIN2EC        ?= jasmin2ec
JASMIN2EC_FLAGS  ?= --array-model=old

JPATH := JASMINPATH="XMSS=../ref-jasmin:Stdlib=../ref-jasmin/stdlib"

# --------------------------------------------------------------------------------------------------

default: extract check_spec check_proofs check_extraction
all: clean distclean extract check_spec check_proofs check_extraction check_xmss_spec \
	check_xmss_mt_spec check_xmss_spec_extra check_correctness_proof check_security_proof \
	check_xmss_spec_equivs
extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------------------------------------

.PHONY: check_spec check_proofs check_extraction check_xmss_spec check_xmss_mt_spec \
        check_correctness_proof check_security_proof check_xmss_spec_extra \
				check_xmss_spec_equivs

# --------------------------------------------------------------------------------------------------

extraction/XMSS_IMPL.ec: ../ref-jasmin/xmss/xmss.jinc | common/
	printf "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > tmp
	cat $< >> tmp
	$(JPATH) $(JASMIN2EC) $(JASMIN2EC_FLAGS) tmp -o $@ || rm tmp # remove the file even when jasmin2ec fails
	rm tmp
	mv extraction/WArray* common/
	mv extraction/Array* common/

# --------------------------------------------------------------------------------------------------

check_xmss_common_spec:
	$(ECRUNTEST) config/tests.config common-spec

check_xmss_spec:
	$(ECRUNTEST) config/tests.config xmss-spec

check_xmss_mt_spec:
	$(ECRUNTEST) config/tests.config xmss-mt-spec

check_spec:  check_xmss_common_spec check_xmss_spec check_xmss_mt_spec

check_extraction: extraction/XMSS_IMPL.ec
	$(ECRUNTEST) config/tests.config extraction

################################### correctness proof ##############################################

check_correctness_proof: extraction/XMSS_IMPL.ec
	$(ECRUNTEST) config/tests.config correctness

####################################################################################################

check_security_proof:
	$(ECRUNTEST) config/tests.config security

####################################################################################################

check_xmss_spec_extra:
	$(ECRUNTEST) config/tests.config spec-extra

check_xmss_spec_equivs:
	$(ECRUNTEST) config/tests.config spec-equivs

check_proofs: check_xmss_spec_extra checks_xmss_spec_equivs check_correctness_proof check_security_proof

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	-$(RM) -r *.eco *~ \#*\# spec/xmss/*.eco spec/xmss/*~ \
	spec/xmss/\#*\# spec/xmss_mt/*.eco spec/xmss_mt/*~ spec/xmss_mt/\#*\# \
	correctness/*.eco correctness/*~ correctness/\#*\# security/*/*.eco

.PHONY: distclean
distclean:
	-$(RM) -r extraction/XMSS_IMPL.ec common/

# --------------------------------------------------------------------------------------------------

extraction/ common/:
	mkdir -p $@
