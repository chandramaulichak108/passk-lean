// Lean compiler output
// Module: PassK.Definitions
// Imports: public import Init public meta import Init public import PassK.Values
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
extern lean_object* lp_mathlib_NNReal_instSemilatticeSup;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
lean_object* lp_mathlib_Finset_sup___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_passk_x2dformalization_PassK_Finite_demonstratorValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_optimalValue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_optimalValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_optimalValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_demonstratorGap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_demonstratorGap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal___redArg___lam__0(lean_object* v_r_1_, lean_object* v_x_2_, lean_object* v_y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_r_1_, v_x_2_, v_y_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal___redArg(lean_object* v_inst_5_, lean_object* v_r_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___f_8_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_8_, 0, v_r_6_);
lean_closure_set(v___f_8_, 1, v_x_7_);
v___x_9_ = lp_mathlib_NNReal_instSemilatticeSup;
v___x_10_ = lp_mathlib_Real_definition_00___x40_Mathlib_Basic_Real_Basic_3335671075____hygCtx___hyg_2_;
v___x_11_ = lp_mathlib_Finset_sup___redArg(v___x_9_, v___x_10_, v_inst_5_, v___f_8_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal(lean_object* v_X_12_, lean_object* v_Y_13_, lean_object* v_inst_14_, lean_object* v_r_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal___redArg(v_inst_14_, v_r_15_, v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_optimalValue___redArg___lam__0(lean_object* v_contexts_18_, lean_object* v_inst_19_, lean_object* v_r_20_, lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___f_24_; 
lean_inc(v_x_21_);
v___x_22_ = lean_apply_1(v_contexts_18_, v_x_21_);
v___x_23_ = lp_passk_x2dformalization_PassK_Finite_pointwiseOptimal___redArg(v_inst_19_, v_r_20_, v_x_21_);
v___f_24_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_24_, 0, v___x_22_);
lean_closure_set(v___f_24_, 1, v___x_23_);
return v___f_24_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_optimalValue___redArg(lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_contexts_27_, lean_object* v_r_28_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_29_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_Finite_optimalValue___redArg___lam__0), 4, 3);
lean_closure_set(v___f_29_, 0, v_contexts_27_);
lean_closure_set(v___f_29_, 1, v_inst_26_);
lean_closure_set(v___f_29_, 2, v_r_28_);
v___x_30_ = lp_mathlib_Real_instAddCommMonoid;
v___x_31_ = lp_mathlib_Finset_sum___redArg(v___x_30_, v_inst_25_, v___f_29_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_optimalValue(lean_object* v_X_32_, lean_object* v_Y_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_contexts_36_, lean_object* v_r_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_passk_x2dformalization_PassK_Finite_optimalValue___redArg(v_inst_34_, v_inst_35_, v_contexts_36_, v_r_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_demonstratorGap___redArg(lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_contexts_41_, lean_object* v_demo_42_, lean_object* v_r_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___f_46_; lean_object* v___f_47_; 
lean_inc(v_r_43_);
lean_inc(v_contexts_41_);
lean_inc(v_inst_40_);
lean_inc(v_inst_39_);
v___x_44_ = lp_passk_x2dformalization_PassK_Finite_optimalValue___redArg(v_inst_39_, v_inst_40_, v_contexts_41_, v_r_43_);
v___x_45_ = lp_passk_x2dformalization_PassK_Finite_demonstratorValue___redArg(v_inst_39_, v_inst_40_, v_contexts_41_, v_demo_42_, v_r_43_);
v___f_46_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_46_, 0, v___x_45_);
v___f_47_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_47_, 0, v___x_44_);
lean_closure_set(v___f_47_, 1, v___f_46_);
return v___f_47_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_demonstratorGap(lean_object* v_X_48_, lean_object* v_Y_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_contexts_52_, lean_object* v_demo_53_, lean_object* v_r_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_passk_x2dformalization_PassK_Finite_demonstratorGap___redArg(v_inst_50_, v_inst_51_, v_contexts_52_, v_demo_53_, v_r_54_);
return v___x_55_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Values(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_passk_x2dformalization_PassK_Definitions(uint8_t builtin) {
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
res = initialize_passk_x2dformalization_PassK_Values(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
