// Lean compiler output
// Module: PassK.FiniteTesting
// Imports: public import Init public meta import Init public import PassK.FiniteTail
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_326038627____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_distributionOverlap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_distributionOverlap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_distributionOverlap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_distributionOverlap___redArg___lam__0(lean_object* v_p_u2080_1_, lean_object* v_p_u2081_2_, lean_object* v_00_u03c9_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___f_6_; 
lean_inc(v_00_u03c9_3_);
v___x_4_ = lean_apply_1(v_p_u2080_1_, v_00_u03c9_3_);
v___x_5_ = lean_apply_1(v_p_u2081_2_, v_00_u03c9_3_);
v___f_6_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_326038627____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_6_, 0, v___x_4_);
lean_closure_set(v___f_6_, 1, v___x_5_);
return v___f_6_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_distributionOverlap___redArg(lean_object* v_inst_7_, lean_object* v_p_u2080_8_, lean_object* v_p_u2081_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___f_10_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_Finite_distributionOverlap___redArg___lam__0), 3, 2);
lean_closure_set(v___f_10_, 0, v_p_u2080_8_);
lean_closure_set(v___f_10_, 1, v_p_u2081_9_);
v___x_11_ = lp_mathlib_Real_instAddCommMonoid;
v___x_12_ = lp_mathlib_Finset_sum___redArg(v___x_11_, v_inst_7_, v___f_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_distributionOverlap(lean_object* v_00_u03a9_13_, lean_object* v_inst_14_, lean_object* v_p_u2080_15_, lean_object* v_p_u2081_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_passk_x2dformalization_PassK_Finite_distributionOverlap___redArg(v_inst_14_, v_p_u2080_15_, v_p_u2081_16_);
return v___x_17_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_FiniteTail(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_passk_x2dformalization_PassK_FiniteTesting(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_FiniteTail(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
