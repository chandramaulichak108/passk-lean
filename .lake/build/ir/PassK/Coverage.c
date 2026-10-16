// Lean compiler output
// Module: PassK.Coverage
// Imports: public import Init public meta import Init public import Mathlib
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
lean_object* lp_mathlib_Multiset_map___redArg(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_sum___at___00Finset_sum___at___00BoundingSieve_multSum_spec__0_spec__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndunion___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_weight___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_Finset_sum___at___00PassK_weight_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_weight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_weight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_Finset_sum___at___00PassK_weight_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_weight___redArg___lam__0(lean_object* v_w_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_w_1_, v_a_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_Finset_sum___at___00PassK_weight_spec__0___redArg(lean_object* v_s_4_, lean_object* v_f_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lp_mathlib_Multiset_map___redArg(v_f_5_, v_s_4_);
v___x_7_ = lp_mathlib_Multiset_sum___at___00Finset_sum___at___00BoundingSieve_multSum_spec__0_spec__0(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_weight___redArg(lean_object* v_w_8_, lean_object* v_s_9_){
_start:
{
lean_object* v___f_10_; lean_object* v___x_11_; 
v___f_10_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_weight___redArg___lam__0), 2, 1);
lean_closure_set(v___f_10_, 0, v_w_8_);
v___x_11_ = lp_passk_x2dformalization_Finset_sum___at___00PassK_weight_spec__0___redArg(v_s_9_, v___f_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_weight(lean_object* v_00_u03b1_12_, lean_object* v_w_13_, lean_object* v_s_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_passk_x2dformalization_PassK_weight___redArg(v_w_13_, v_s_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_Finset_sum___at___00PassK_weight_spec__0(lean_object* v_00_u03b9_16_, lean_object* v_s_17_, lean_object* v_f_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_passk_x2dformalization_Finset_sum___at___00PassK_weight_spec__0___redArg(v_s_17_, v_f_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix___redArg(lean_object* v_inst_20_, lean_object* v_A_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_zero_23_; uint8_t v_isZero_24_; 
v_zero_23_ = lean_unsigned_to_nat(0u);
v_isZero_24_ = lean_nat_dec_eq(v_x_22_, v_zero_23_);
if (v_isZero_24_ == 1)
{
lean_object* v___x_25_; 
lean_dec(v_A_21_);
lean_dec_ref(v_inst_20_);
v___x_25_ = lean_box(0);
return v___x_25_;
}
else
{
lean_object* v_one_26_; lean_object* v_n_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_one_26_ = lean_unsigned_to_nat(1u);
v_n_27_ = lean_nat_sub(v_x_22_, v_one_26_);
lean_inc(v_A_21_);
lean_inc_ref(v_inst_20_);
v___x_28_ = lp_passk_x2dformalization_PassK_coveragePrefix___redArg(v_inst_20_, v_A_21_, v_n_27_);
v___x_29_ = lean_apply_1(v_A_21_, v_n_27_);
v___x_30_ = lp_mathlib_Multiset_ndunion___redArg(v_inst_20_, v___x_28_, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix___redArg___boxed(lean_object* v_inst_31_, lean_object* v_A_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_passk_x2dformalization_PassK_coveragePrefix___redArg(v_inst_31_, v_A_32_, v_x_33_);
lean_dec(v_x_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_, lean_object* v_A_37_, lean_object* v_x_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_passk_x2dformalization_PassK_coveragePrefix___redArg(v_inst_36_, v_A_37_, v_x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_coveragePrefix___boxed(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_A_42_, lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_passk_x2dformalization_PassK_coveragePrefix(v_00_u03b1_40_, v_inst_41_, v_A_42_, v_x_43_);
lean_dec(v_x_43_);
return v_res_44_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_passk_x2dformalization_PassK_Coverage(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
