# -*- Makefile -*-

# --------------------------------------------------------------------
EASYCRYPT   ?= easycrypt
EC_JOBS     ?= 2
EC_FLAGS    ?= -jobs $(EC_JOBS)
ECRUNTEST   ?= $(EASYCRYPT) runtest $(EC_FLAGS)
J2EC        ?= jasmin2ec
J2EC_FLAGS  ?= --array-model=old

JPATH := JASMINPATH="XMSS=../ref-jasmin:Stdlib=../ref-jasmin/stdlib"

# --------------------------------------------------------------------
.PHONY: default all clean distclean __force__

# --------------------------------------------------------------------
default: extract check_all

all: clean distclean extract check_all

extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------
extraction/XMSS_IMPL.ec: ../ref-jasmin/xmss/xmss.jinc
	$(eval TMP := $(shell mktemp -d))
	printf "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > $(TMP)/input.jazz
	cat $< >> $(TMP)/input.jazz
	$(JPATH) $(J2EC) $(J2EC_FLAGS) $(TMP)/input.jazz -o $@
	rm -rf $(TMP)
	mv extraction/WArray* common/
	mv extraction/Array* common/

# --------------------------------------------------------------------
check_%: __force__
	$(ECRUNTEST) config/tests.config $(subst _,-,$*)

# --------------------------------------------------------------------
clean:
	find . -name '*.eco' -print0 | xargs -0 rm -f

distclean: clean
	rm -f extraction/XMSS_IMPL.ec common/*.ec common/*.eca
