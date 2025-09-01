# -*- Makefile -*-

# --------------------------------------------------------------------
EASYCRYPT  ?= easycrypt
EC_FLAGS   ?= -jobs 1
ECRUNTEST  ?= $(EASYCRYPT) runtest $(EC_FLAGS)

JASMIN2EC        ?= jasmin2ec
JASMIN2EC_FLAGS  ?= --array-model=old

JPATH := JASMINPATH="XMSS=../ref-jasmin:Stdlib=../ref-jasmin/stdlib"

# --------------------------------------------------------------------
.PHONY: default all clean distclean __force__

# --------------------------------------------------------------------
default: extract check_all

all: clean distclean extract check_all

extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------
extraction/XMSS_IMPL.ec: ../ref-jasmin/xmss/xmss.jinc
	printf "from XMSS require \"params/params-xmssmt-sha2_20_2_256.jinc\"" > tmp
	cat $< >> tmp
	$(JPATH) $(JASMIN2EC) $(JASMIN2EC_FLAGS) tmp -o $@ || rm tmp # remove the file even when jasmin2ec fails
	rm tmp
	mv extraction/WArray* common/
	mv extraction/Array* common/

# --------------------------------------------------------------------
check_%: __force__
	$(ECRUNTEST) config/tests.config $*

# --------------------------------------------------------------------
clean:
	-$(RM) -r *.eco *~ \#*\# spec/xmss/*.eco spec/xmss/*~ \
	spec/xmss/\#*\# spec/xmss_mt/*.eco spec/xmss_mt/*~ spec/xmss_mt/\#*\# \
	correctness/*.eco correctness/*~ correctness/\#*\# security/*/*.eco

distclean:
	-$(RM) -r extraction/XMSS_IMPL.ec common/*.ec common/*.eca
