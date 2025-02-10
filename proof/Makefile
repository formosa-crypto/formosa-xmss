# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction -I spec -I correctness -I security
EC_FLAGS   ?= -timeout 20 $(EC_INCLUDE) ${ECADDFLAGS}

JASMIN2EC        ?= jasmin2ec
JASMIN2EC_FLAGS  ?= --array-model=old

JPP          := ../submodules/jasmin-preprocessor/jpp
PREPROCESSOR := ../submodules/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

default: extract check_spec check_proofs check_extraction
all: clean distclean extract check_spec check_proofs check_extraction
extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------------------------------------

.PHONY: check_spec check_proofs check_extraction check_xmss_spec check_xmss_mt_spec \
        check_correctness_proof check_security_proof check_xmss_xmssmt_proof

# --------------------------------------------------------------------------------------------------

common/Array8.ec: | common/
	echo "from Jasmin require import JArray.\n\nclone export PolyArray as Array8  with op size <- 8.\n" > $@

extraction/XMSS_IMPL.ec: extraction/XMSS_IMPL.jazz | common/
	$(JASMIN2EC) $(JASMIN2EC_FLAGS) $< -o $@
	mv extraction/WArray* common/
	mv extraction/Array* common/

# --------------------------------------------------------------------------------------------------

check_xmss_spec: common/Array8.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/BaseW.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Hash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/LTree.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Types.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/WOTS.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_PRF.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_TreeHash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_Types.ec

check_xmss_mt_spec: common/Array8.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/BaseW.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Hash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/LTree.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Types.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/WOTS.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_PRF.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_TreeHash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_Types.ec

check_spec: check_xmss_spec check_xmss_mt_spec

check_extraction: extraction/XMSS_IMPL.ec 
	$(EASYCRYPT) $(EC_INCLUDE) $<

################################### correctness proof ##############################################

# The targets check_c_* are used to check the correctness proof files 
check_c_%: extraction/XMSS_IMPL.ec
	$(EASYCRYPT) $(EC_FLAGS) correctness/$*.ec

CORRECTNESS_PROOF_FILES := $(addprefix check_c_, $(notdir $(basename $(wildcard correctness/*.ec))))

check_correctness_proof: extraction/XMSS_IMPL.ec $(CORRECTNESS_PROOF_FILES)

####################################################################################################

# TODO: This could be improved by doing something similar to the the target check_correctness_proof
check_security_proof:
	$(EASYCRYPT) $(EC_FLAGS) security/acai/DigitalSignatures.eca   
	$(EASYCRYPT) $(EC_FLAGS) security/acai/DigitalSignaturesROM.eca
	$(EASYCRYPT) $(EC_FLAGS) security/acai/EUFRMA_Interactive_Equiv.ec  
	$(EASYCRYPT) $(EC_FLAGS) security/acai/FL_XMSS_TW.ec                
	$(EASYCRYPT) $(EC_FLAGS) security/acai/HashAddresses.eca
	$(EASYCRYPT) $(EC_FLAGS) security/acai/HashThenSign.eca 
	$(EASYCRYPT) $(EC_FLAGS) security/acai/KeyedHashFunctions.eca  
	$(EASYCRYPT) $(EC_FLAGS) security/acai/Reprogramming.ec        
	$(EASYCRYPT) $(EC_FLAGS) security/acai/TweakableHashFunctions.eca  
	$(EASYCRYPT) $(EC_FLAGS) security/acai/WOTS_TW_Checksum.ec         
	$(EASYCRYPT) $(EC_FLAGS) security/acai/WOTS_TW.ec
	$(EASYCRYPT) $(EC_FLAGS) security/acai/XMSS_TW.ec
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/DigitalSignatures.eca        
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/DigitalSignaturesROM.eca     
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/EUFRMA_Interactive_Equiv.ec  
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/FL_XMSS_TW.ec                
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/HashThenSign.eca             
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/KeyedHashFunctions.eca
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/Reprogramming.ec
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/TweakableHashFunctions.eca
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/WOTS_TW_Checksum.ec
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/WOTS_TW.ec
	$(EASYCRYPT) $(EC_FLAGS) security/fsai/XMSS_TW.ec

####################################################################################################

check_xmss_xmssmt_proof: common/Array8.ec
	$(EASYCRYPT) $(EC_FLAGS) spec/XMSS_vs_XMSS_MT.ec

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
