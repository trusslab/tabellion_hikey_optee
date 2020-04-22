// SPDX-License-Identifier: BSD-2-Clause
/*
 * Copyright (c) 2015, Linaro Limited
 */
#include <compiler.h>
#include <stdio.h>
#include <trace.h>
#include <kernel/pseudo_ta.h>
#include <mm/tee_pager.h>
#include <mm/tee_mm.h>
#include <string.h>
#include <string_ext.h>
#include <malloc.h>
#include <kernel/pseudo_ta.h>
#include <kernel/tee_common.h>
#include <kernel/tee_misc.h>
#include <kernel/tee_ta_manager.h>
#include <kernel/tee_time.h>
#include <kernel/thread.h>
#include <kernel/user_ta.h>
#include <mm/core_mmu.h>
#include <mm/core_memprot.h>
#include <mm/mobj.h>
#include <mm/tee_mmu.h>
#include <assert.h>
#include <compiler.h>
#include <crypto/crypto.h>
#include <kernel/tee_ta_manager.h>
#include <mm/tee_mmu.h>
#include <stdlib_ext.h>
#include <string_ext.h>
#include <string.h>
#include <sys/queue.h>
#include <tee_api_types.h>
#include <tee/tee_cryp_utl.h>
#include <tee/tee_obj.h>
#include <tee/tee_svc_cryp.h>
#include <tee/tee_svc.h>
#include <trace.h>
#include <utee_defines.h>
#include <util.h>
#include <tee_api_defines_extensions.h>
#include "stats.h"

#define TA_NAME		"stats.ta"

#define STATS_UUID \
		{ 0xd96a5b40, 0xe2c7, 0xb1af, \
			{ 0x87, 0x94, 0x10, 0x02, 0xa5, 0xd5, 0xc6, 0x1b } }
uint8_t t_modulus[] = {
    			0xae, 0xc7, 0x77, 0xbf, 0x4d, 0x38, 0x60, 0xf4, 0xb4, 0x61, 0x11,
			0x21, 0xf6, 0x3c, 0x04, 0x02, 0x56, 0xaa, 0x67, 0xbc, 0xf7, 0x30, 0xc0,
			0x45, 0xa9, 0x2d, 0x61, 0x2c, 0xb4, 0x2a, 0x0a, 0x78, 0xf5, 0xba, 0xe3,
			0x6e, 0x69, 0x7e, 0xfd, 0x2e, 0xb5, 0x13, 0x85, 0x1b, 0x9e, 0x9b, 0xc0,
			0x91, 0xe5, 0x12, 0xf8, 0xdf, 0xce, 0xf2, 0x40, 0x77, 0x31, 0x8f, 0xee,
			0x5f, 0x9b, 0x1a, 0xe9, 0x9a, 0x99, 0xab, 0xbb, 0x57, 0x18, 0xdf, 0x41,
			0x79, 0xfb, 0xeb, 0x7c, 0x7d, 0x30, 0xa8, 0x10, 0xdb, 0x9e, 0x82, 0xae,
			0x1f, 0xca, 0x15, 0xde, 0xc9, 0x1e, 0x1c, 0x94, 0xfe, 0x25, 0xcb, 0x2b,
			0xa7, 0xcc, 0xf8, 0x51, 0x11, 0x73, 0x65, 0xfe, 0xa0, 0x7f, 0x82, 0xfb,
			0x1d, 0x80, 0xd6, 0xd8, 0x55, 0xd7, 0x36, 0xf1, 0x5a, 0x4b, 0xe9, 0x8f,
			0xaf, 0x88, 0x87, 0xfc, 0xff, 0xd7, 0x50, 0x63, 0x43,
		      };
#define PRI_FAIL(str, ...) IMSG("Error: %s", str);
#define PRI_OK(str, ...) IMSG("OK: %s", str);

#define SIZE_OF_VEC(vec) (sizeof(vec) - 1)

TEE_UUID *uuid;
uint8_t t_public_exp[] = "\x01\x00\x01";

uint8_t t_private_exp[] =
    "\x34\x3e\x7f\xb6\xf9\x58\x2e\xf3\x36\xb0\x05\x35\x07\xab\xac"
    "\xef\x1e\x04\xd5\xf9\x90\x52\x4c\x47\x06\x69\x00\x31\x22\xb1"
    "\xa6\x6b\xbd\xd8\x5d\x7f\x75\x9d\x76\x04\xee\x2f\xa5\x8c\x39"
    "\xff\x08\xb3\x13\xac\x76\x24\x40\x71\xfd\x7f\x23\x9b\x88\x7f"
    "\x9f\x97\x8d\xd8\x20\x14\x9b\x9c\x98\xf3\x5c\x48\x62\x02\x9d"
    "\x3f\x6a\xb5\x28\x33\xf7\x3c\x87\xef\x2a\x83\xcc\x68\x97\x8d"
    "\x0c\x2c\x17\xd8\xae\x07\xf8\x6b\xb1\xf2\xc6\x19\x8c\xad\x81"
    "\x1a\xf5\x83\x1b\xf3\x91\xe6\x61\x1b\xf1\x7c\xc2\xac\xb3\xe1"
    "\xfc\x3d\x89\x16\x5f\x2f\xb3\x81";

/* Global variables */
int display_state = 0;
int photo_state = 0;
bool time_synched = 1;

enum cryp_state {
        CRYP_STATE_INITIALIZED = 0,
        CRYP_STATE_UNINITIALIZED
};
typedef void (*tee_cryp_ctx_finalize_func_t) (void *ctx);
struct tee_cryp_state {
        TAILQ_ENTRY(tee_cryp_state) link;
        uint32_t algo;
        uint32_t mode;
        vaddr_t key1;
        vaddr_t key2;
        void *ctx;
        tee_cryp_ctx_finalize_func_t ctx_finalize;
        enum cryp_state state;
};

static int calc_digest(uint32_t hash_alg,
		       void *msg,
		       uint32_t msg_len,
		       void *hash,
		       uint32_t *hash_len)
{
	TEE_Result ret;
	void *ctx = NULL;

	IMSG("%s\n", __FUNCTION__);
	ret = crypto_hash_alloc_ctx(&ctx, TEE_ALG_SHA256);
	if (ret != TEE_SUCCESS) {
		PRI_FAIL("Failed allocate digest operation");
		return 1;
	}

	IMSG("%s\n", __FUNCTION__);
        ret = crypto_hash_init(ctx);
        if (ret)
                return ret;

	IMSG("%s\n", __FUNCTION__);
	if (msg_len) {
		ret = crypto_hash_update(ctx, msg, msg_len);
		if (ret != TEE_SUCCESS)
			return ret;
	}

	IMSG("%s\n", __FUNCTION__);
	ret = crypto_hash_final(ctx, hash, *hash_len);
	if (ret != TEE_SUCCESS)
		return ret;

	crypto_hash_free_ctx(ctx);
	IMSG("%s\n", __FUNCTION__);
	return 0;
}

struct tee_cryp_obj_type_props {
        TEE_ObjectType obj_type;
        uint16_t min_size;      /* may not be smaller than this */
        uint16_t max_size;      /* may not be larger than this */
        uint16_t alloc_size;    /* this many bytes are allocated to hold data */
        uint8_t quanta;         /* may only be an multiple of this */

        uint8_t num_type_attrs;
        const struct tee_cryp_obj_type_attrs *type_attrs;
};


extern const struct tee_cryp_obj_type_props *tee_svc_find_type_props(
                TEE_ObjectType obj_type);

extern TEE_Result tee_svc_cryp_obj_populate_type(
                struct tee_obj *o,
                const struct tee_cryp_obj_type_props *type_props,
                const TEE_Attribute *attrs,
                uint32_t attr_count);

int warp_asym_op(struct tee_obj *key,
			TEE_OperationMode mode,
			uint32_t alg,
			TEE_Attribute *params,
			uint32_t paramCount,
			void *in_chunk,
			uint32_t in_chunk_len,
			void *out_chunk,
			uint32_t *out_chunk_len)
{
	TEE_Result ret = TEE_SUCCESS;
	int salt_len;

	IMSG("%s\n", __FUNCTION__);
	salt_len = in_chunk_len;

	if (mode == TEE_MODE_SIGN) {
		ret = crypto_acipher_rsassa_sign(TEE_ALG_RSASSA_PKCS1_PSS_MGF1_SHA256, key->attr, salt_len,
					 in_chunk, in_chunk_len, out_chunk,
					 out_chunk_len);

		if (ret != TEE_SUCCESS) {
			PRI_FAIL("Sign failed : 0x%x", ret);
			goto err;
		}

	} else if (mode == TEE_MODE_VERIFY) {
		ret = crypto_acipher_rsassa_verify(TEE_ALG_RSASSA_PKCS1_V1_5_SHA256, key->attr, salt_len,
					 in_chunk, in_chunk_len, out_chunk,
					 out_chunk_len);

		if (ret != TEE_SUCCESS) {
			PRI_FAIL("Verify failed : 0x%x", ret);
			goto err;
		}
	}
	else {
		goto err;
	}

	return 0;

err:
	return 1;
}


void print_hex_memory(void *mem) {
	int i;
	unsigned char *p = (unsigned char *)mem;
	for (i=0;i<128;i++) {
		IMSG("0x%02x ", p[i]);
		if ((i%16==0) && i)
			IMSG("\n");
	}
	IMSG("\n");
}
void *start_time, *start_timem, *time_range, *time_rangem;
void *nonce; /* nonce for time synchronization */
void *notary_cert;

/* Sign fb or the cam buffer */
static uint32_t rsa_sign(unsigned char *buf, uint32_t buf_len, char signature[], uint32_t signature_len)
{
	struct tee_obj *o;
	TEE_Result ret = TEE_SUCCESS;
	char hash[64] = {0}; /*sha256*/
	uint32_t hash_len = 32;
	TEE_Attribute rsa_attrs[3];
	uint32_t rsa_alg = TEE_ALG_RSASSA_PKCS1_V1_5_SHA256, fn_ret = 1; /* Init error return */;

	/* Modulo */
	rsa_attrs[0].attributeID = TEE_ATTR_RSA_MODULUS;
	rsa_attrs[0].content.ref.buffer = t_modulus;
	rsa_attrs[0].content.ref.length = SIZE_OF_VEC(t_modulus) + 1;

	/* Public exp */
	rsa_attrs[1].attributeID = TEE_ATTR_RSA_PUBLIC_EXPONENT;
	rsa_attrs[1].content.ref.buffer = t_public_exp;
	rsa_attrs[1].content.ref.length = SIZE_OF_VEC(t_public_exp);

	/* Private exp */
	rsa_attrs[2].attributeID = TEE_ATTR_RSA_PRIVATE_EXPONENT;
	rsa_attrs[2].content.ref.buffer = t_private_exp;
	rsa_attrs[2].content.ref.length = SIZE_OF_VEC(t_private_exp);

	IMSG("%s\n", __FUNCTION__);
	o = tee_obj_alloc();
	if (!o)
		return TEE_ERROR_OUT_OF_MEMORY;

	IMSG("%s\n", __FUNCTION__);
	ret = tee_obj_set_type(o, TEE_TYPE_RSA_KEYPAIR, 1024);
	if (ret != TEE_SUCCESS) {
		tee_obj_free(o);
		return ret;
	}

	IMSG("%s\n", __FUNCTION__);
	ret = tee_svc_cryp_obj_populate_type(o, tee_svc_find_type_props(TEE_TYPE_RSA_KEYPAIR), rsa_attrs, 3);
	if (ret == TEE_SUCCESS)
		o->info.handleFlags |= TEE_HANDLE_FLAG_INITIALIZED;


	IMSG("rsa_sign[2]\n");
	if (calc_digest(TEE_ALG_SHA256, buf, buf_len, hash, &hash_len))
		goto err;

	if (warp_asym_op(o, TEE_MODE_SIGN, rsa_alg, (TEE_Attribute *)NULL, 0,
			 (void *)hash, hash_len, (void *)signature, &signature_len))
		goto err;
	IMSG("Signature length: %d\n\n", signature_len);

	fn_ret = 0; /* OK */

err:
	tee_obj_attr_free(o);

	return fn_ret;
}

static uint32_t rsa_verify_sign(unsigned char *buf, uint32_t buf_len, char signature[], uint32_t signature_len)
{
	struct tee_obj *o;
	TEE_Result ret = TEE_SUCCESS;
	char hash[64] = {0}; /*sha256*/
	uint32_t hash_len = 32;
	TEE_Attribute rsa_attrs[3];
	uint32_t rsa_alg = TEE_ALG_RSASSA_PKCS1_V1_5_SHA256, fn_ret = 1; /* Init error return */;

	/* Modulo */
	rsa_attrs[0].attributeID = TEE_ATTR_RSA_MODULUS;
	rsa_attrs[0].content.ref.buffer = t_modulus;
	rsa_attrs[0].content.ref.length = SIZE_OF_VEC(t_modulus) + 1;

	/* Public exp */
	rsa_attrs[1].attributeID = TEE_ATTR_RSA_PUBLIC_EXPONENT;
	rsa_attrs[1].content.ref.buffer = t_public_exp;
	rsa_attrs[1].content.ref.length = SIZE_OF_VEC(t_public_exp);

	/* Private exp */
	rsa_attrs[2].attributeID = TEE_ATTR_RSA_PRIVATE_EXPONENT;
	rsa_attrs[2].content.ref.buffer = t_private_exp;
	rsa_attrs[2].content.ref.length = SIZE_OF_VEC(t_private_exp);

	o = tee_obj_alloc();
	if (!o)
		return TEE_ERROR_OUT_OF_MEMORY;

	ret = tee_obj_set_type(o, TEE_TYPE_RSA_KEYPAIR, 1024);
	if (ret != TEE_SUCCESS) {
		tee_obj_free(o);
		return ret;
	}

	ret = tee_svc_cryp_obj_populate_type(o, tee_svc_find_type_props(TEE_TYPE_RSA_KEYPAIR), rsa_attrs, 3);
	if (ret == TEE_SUCCESS)
		o->info.handleFlags |= TEE_HANDLE_FLAG_INITIALIZED;


//	IMSG("rsa_sign[2]\n");
	if (calc_digest(TEE_ALG_SHA256, buf, buf_len, hash, &hash_len))
		goto err;

//	IMSG("rsa_sign[3]\n");
	if (warp_asym_op(o, TEE_MODE_VERIFY, rsa_alg, (TEE_Attribute *)NULL, 0,
			 (void *)hash, hash_len, (void *)signature, &signature_len))
		goto err;
//	IMSG("Signature length: %d\n\n", signature_len);

	fn_ret = 0; /* OK */

err:
	tee_obj_attr_free(o);
	return fn_ret;
}

static TEE_Result sync_start(uint32_t param_types,
	TEE_Param params[4])
{
	uint32_t exp_param_types = TEE_PARAM_TYPES(TEE_PARAM_TYPE_VALUE_INOUT,
						   TEE_PARAM_TYPE_VALUE_INOUT,
						   TEE_PARAM_TYPE_NONE,
						   TEE_PARAM_TYPE_NONE);
	TEE_Time t;

	IMSG("SaeedTA: sync_start***************\n");
	if (param_types != exp_param_types)
		return TEE_ERROR_BAD_PARAMETERS;


	/* set the T1 in NTP protocol */
	if(!start_time) {
		start_time = calloc(1, 4);
		start_timem = calloc(1, 4);
		time_range = calloc(1, 4);
		time_rangem = calloc(1, 4);
		notary_cert = calloc(1, 128);
	}

	if (uuid) {
		tee_time_get_ta_time(uuid, &t);
		tee_time_set_ta_time(uuid, &t);

		*(uint32_t*)start_time = t.seconds;
		*(uint32_t*)start_timem = t.millis;
	}
	else {
		tee_time_get_sys_time(&t);

		*(uint32_t*)start_time = t.seconds;
		*(uint32_t*)start_timem = t.millis;	
	}

	if (!nonce) {
		nonce = calloc(1, 4);
	}

	/* setting the nonce to be sent to the time server */
	crypto_rng_read(nonce, 4);

	/* return nonce to the normal world */
	params[0].value.a = *(int*)nonce;
	
	return TEE_SUCCESS;
}

#define TEE_TIME_ADD(t1, t2, dst) do {                      \
        (dst).seconds = (t1).seconds + (t2).seconds;        \
        (dst).millis = (t1).millis + (t2).millis;           \
        if ((dst).millis >= TEE_TIME_MILLIS_BASE) {         \
            (dst).seconds++;                                \
            (dst).millis -= TEE_TIME_MILLIS_BASE;           \
        }                                                   \
    } while (0)

#define TEE_TIME_SUB(t1, t2, dst) do {                      \
        (dst).seconds = (t1).seconds - (t2).seconds;        \
        if ((t1).millis < (t2).millis) {                    \
            (dst).seconds--;                                \
            (dst).millis = (t1).millis + TEE_TIME_MILLIS_BASE - (t2).millis;\
        } else {                                            \
            (dst).millis = (t1).millis - (t2).millis;       \
        }                                                   \
    } while (0)

static TEE_Result sync_server(uint32_t param_types,
	TEE_Param params[4])
{
	uint32_t* src;
	uint32_t t1, t2, t3, t4;
	uint32_t t1m, t2m, t3m, t4m; //milliseconds
	TEE_Time T1, T2, T3, T4, range, cinterval;
	TEE_Time tmp1, tmp2;
	TEE_Time t;
	unsigned char sig_buf[128];
	uint32_t buf[4];

	src = params[0].memref.buffer;

	t1 = *(uint32_t*)start_time;
	t1m = *(uint32_t*)start_timem;

	//IMSG("DEBUG[1]\n");
	t2 = *src;
	src++;
	t2m = *src;
	src++;
	t3 = *src;
	src++;
	t3m = *src;
	src++;

	/* Get signature buf */
	memcpy(sig_buf, src, 128);

	if (uuid)
		tee_time_get_ta_time(uuid, &T4);
	else
		tee_time_get_sys_time(&T4);

	t4 = T4.seconds;
	t4m = T4.millis;
	//IMSG("Saeed ta persistent time [1]: seconds=%u, milli=%u\n", T4.seconds, T4.millis);

	T1.seconds = t1;
	T1.millis = t1m;
	T2.seconds = t2;
	T2.millis = (t2m*1000)/4294967296;
	T3.seconds = t3;
	T3.millis = (t3m*1000)/4294967296;

	/* Verify the signature received from server. */
	buf[0] = t2;
	buf[1] = t2m;
	buf[2] = t3;
	buf[3] = t3m;
	rsa_verify_sign((unsigned char*)buf, sizeof(buf), sig_buf, sizeof(sig_buf));

	/* Confidence interval */
	TEE_TIME_SUB(T4, T1, tmp1);
	TEE_TIME_SUB(T2, T3, tmp2);
	TEE_TIME_ADD(tmp1, tmp2, range);

	/* Set the range */
	*(uint32_t*)time_range = range.seconds;
	*(uint32_t*)time_rangem = range.millis;

	if (uuid) {
		tee_time_set_ta_time(uuid, &T3);
		tee_time_get_ta_time(uuid, &t);
	}

	time_synched = 1;

	return TEE_SUCCESS;
}

static TEE_Result sign_fb(uint32_t param_types,
	TEE_Param params[4])
{
	unsigned char sig_buf[128];
	void *sfb, *sfb_paddr, *dis_reg;
	TEE_Time T;
	uint32_t t, tm;
	void *ret_buf; /* For passing back the signature and time */
	void *tmp;
	bool is_photo = 0;

	/* Check if time is synchronized already */
	if(!time_synched) {
		IMSG("Error: Synch time first!%s\n");
		return TEE_SUCCESS;
	}

	/* Get current time of signing */
	if (uuid)
		tee_time_get_ta_time(uuid, &T);
	else
		tee_time_get_sys_time(&T);

	t = T.seconds; /* current time in seconds */
	tm = T.millis; /* current time in milliseconds */

	core_mmu_add_mapping(MEM_AREA_IO_NSEC, 0xf4100000, 1); /* map one page */
	dis_reg = phys_to_virt(0xf4100000 + 0x1008, MEM_AREA_IO_NSEC); /* disp controller reg_addr */
	
	sfb_paddr = *(unsigned int*)dis_reg;

	core_mmu_add_mapping(MEM_AREA_RAM_NSEC, sfb_paddr, 1536); /* 6291456=1536*4096 */

	sfb = phys_to_virt(sfb_paddr, MEM_AREA_RAM_NSEC);
	if(!sfb) {
		IMSG("SW: sfb is NULL\n");
		return 0;
	}

	if (!notary_cert) {
		notary_cert = calloc(1, 128);
	}

	memcpy(notary_cert, params[0].memref.buffer, 128);

	rsa_sign(sfb, 256 * 4096, sig_buf, sizeof(sig_buf));
	
	/* Send back the signature, time, time range, and certif to normal world */
	tmp = params[0].memref.buffer;
	
	memcpy(tmp, sfb, 256 * 4096); /* the captured screenshot */
	tmp += 256 * 4096;

	memcpy(tmp, sig_buf, sizeof(sig_buf)); /* signature */
	tmp += sizeof(sig_buf);

	memcpy(tmp, &t, 4); /* time */
	tmp += 4;

	memcpy(tmp, &tm, 4);
	tmp += 4;

	memcpy(tmp, &time_range, 4); /* confidence interval */
	tmp += 4;

	memcpy(tmp, &time_rangem, 4);
	tmp += 4;

	memcpy(tmp, &is_photo, 1); /* photo or screenshot */
	tmp += 1;

	memcpy(tmp, notary_cert, 128); /* notary certificate */
	
	return TEE_SUCCESS;
}
static TEE_Result sign_cam(uint32_t param_types,
	TEE_Param params[4])
{
	unsigned char sig_buf[128];
	void *sfb, *sfb_paddr, *dis_reg, *tmp;
	TEE_Time T;
	uint32_t t, tm;
	void *ret_buf; /* For passing back the signature and time */
	bool is_photo = 1;

	/* Check if time is synchronized already */
	if(!time_synched) {
		IMSG("Error: Synch time first!%s\n");
		return TEE_SUCCESS;
	}

	/* Get current time of signing */
	if (uuid)
		tee_time_get_ta_time(uuid, &T);
	else
		tee_time_get_sys_time(&T);

	t = T.seconds; /* current time in seconds */
	tm = T.millis; /* current time in milliseconds */

	core_mmu_add_mapping(MEM_AREA_IO_NSEC, 0xf4100000, 1); /* map one page */
	dis_reg = phys_to_virt(0xf4100000 + 0x1008, MEM_AREA_IO_NSEC); /* disp controller reg_addr */
	
	sfb_paddr = *(unsigned int*)dis_reg;

	core_mmu_add_mapping(MEM_AREA_RAM_NSEC, sfb_paddr, 1536); /* 6291456=1536*4096 */

	sfb = phys_to_virt(sfb_paddr, MEM_AREA_RAM_NSEC);
	
	if(!sfb) {
		IMSG("SW: sfb is NULL\n");
		return 0;
	}

	rsa_sign(sfb, 256 * 4096, sig_buf, sizeof(sig_buf));
	
	/* Send back the signature, time, time range, and certif to normal world */
	tmp = params[0].memref.buffer;

	memcpy(tmp, sfb, 256 * 4096); /* the captured screenshot */
	tmp += 256 * 4096;

	memcpy(tmp, sig_buf, sizeof(sig_buf)); /* signature */
	tmp += sizeof(sig_buf);

	memcpy(tmp, &t, 4); /* time */
	tmp += 4;

	memcpy(tmp, &tm, 4);
	tmp += 4;

	memcpy(tmp, &time_range, 4); /* confidence interval */
	tmp += 4;

	memcpy(tmp, &time_rangem, 4);
	tmp += 4;

	memcpy(tmp, &is_photo, 1); /* photo or screenshot */
	
	return TEE_SUCCESS;
}

static TEE_Result open_session(uint32_t nParamTypes __unused,
                               TEE_Param pParams[TEE_NUM_PARAMS] __unused,
                               void **ppSessionContext __unused)
{
        struct tee_ta_session *s = tee_ta_get_calling_session();

        if (s && (s->ctx->flags)) {
                DMSG("open entry point for pseudo-TA \"");
		uuid = &s->ctx->flags;
                return TEE_SUCCESS;
        }
}

/*
 * Trusted Application Entry Points
 */
#define LOG     DMSG_RAW
static TEE_Result invoke_command(void *psess __unused,
				 uint32_t cmd, uint32_t ptypes,
				 TEE_Param params[TEE_NUM_PARAMS])
{
	switch (cmd) {
	case TA_SYNC_START:
		sync_start(ptypes, params);		
		return TEE_SUCCESS;
	case TA_SYNC_SERVER:
		sync_server(ptypes, params);
		return TEE_SUCCESS;
	case TA_SIGN_FB:
		sign_fb(ptypes, params);
		return TEE_SUCCESS;
	case TA_SIGN_CAM:
		sign_cam(ptypes, params);
		return TEE_SUCCESS;
	default:
		return TEE_ERROR_BAD_PARAMETERS;
	}
}

pseudo_ta_register(.uuid = STATS_UUID, .name = TA_NAME,
		   .flags = PTA_DEFAULT_FLAGS,
		   .open_session_entry_point = open_session,
		   .invoke_command_entry_point = invoke_command);
