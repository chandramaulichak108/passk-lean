// Lean compiler output
// Module: PassK.OneStepIID
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
lean_object* lp_passk_x2dformalization_PassK_Finite_bestReward___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Fintype_piFinset___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommMonoid;
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_x_2_){
_start:
{
lean_inc(v_inst_1_);
return v_inst_1_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__0___boxed(lean_object* v_inst_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__0(v_inst_3_, v_x_4_);
lean_dec(v_x_4_);
lean_dec(v_inst_3_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__1(lean_object* v_snapshot_6_, lean_object* v_x_7_, lean_object* v_r_8_, lean_object* v_y_9_, lean_object* v_k_10_, lean_object* v_ys_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___f_17_; 
lean_inc(v_ys_11_);
lean_inc_n(v_x_7_, 2);
v___x_12_ = lean_apply_2(v_snapshot_6_, v_x_7_, v_ys_11_);
lean_inc(v_r_8_);
v___x_13_ = lean_apply_2(v_r_8_, v_x_7_, v_y_9_);
v___x_14_ = lp_passk_x2dformalization_PassK_Finite_bestReward___redArg(v_k_10_, v_r_8_, v_x_7_, v_ys_11_);
v___f_15_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_4282658333____hygCtx___hyg_2_), 2, 1);
lean_closure_set(v___f_15_, 0, v___x_14_);
v___f_16_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_2153608522____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_16_, 0, v___x_13_);
lean_closure_set(v___f_16_, 1, v___f_15_);
v___f_17_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_17_, 0, v___x_12_);
lean_closure_set(v___f_17_, 1, v___f_16_);
return v___f_17_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__2(lean_object* v_snapshot_18_, lean_object* v_x_19_, lean_object* v_r_20_, lean_object* v_k_21_, lean_object* v_demo_22_, lean_object* v___x_23_, lean_object* v___f_24_, lean_object* v___x_25_, lean_object* v_y_26_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___f_32_; 
lean_inc(v_k_21_);
lean_inc(v_y_26_);
lean_inc(v_x_19_);
v___f_27_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__1), 6, 5);
lean_closure_set(v___f_27_, 0, v_snapshot_18_);
lean_closure_set(v___f_27_, 1, v_x_19_);
lean_closure_set(v___f_27_, 2, v_r_20_);
lean_closure_set(v___f_27_, 3, v_y_26_);
lean_closure_set(v___f_27_, 4, v_k_21_);
v___x_28_ = lean_apply_2(v_demo_22_, v_x_19_, v_y_26_);
v___x_29_ = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(v___x_29_, 0, v_k_21_);
v___x_30_ = lp_mathlib_Fintype_piFinset___redArg(v___x_29_, v___x_23_, v___f_24_);
v___x_31_ = lp_mathlib_Finset_sum___redArg(v___x_25_, v___x_30_, v___f_27_);
v___f_32_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_32_, 0, v___x_28_);
lean_closure_set(v___f_32_, 1, v___x_31_);
return v___f_32_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__2___boxed(lean_object* v_snapshot_33_, lean_object* v_x_34_, lean_object* v_r_35_, lean_object* v_k_36_, lean_object* v_demo_37_, lean_object* v___x_38_, lean_object* v___f_39_, lean_object* v___x_40_, lean_object* v_y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__2(v_snapshot_33_, v_x_34_, v_r_35_, v_k_36_, v_demo_37_, v___x_38_, v___f_39_, v___x_40_, v_y_41_);
lean_dec_ref(v___x_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__3(lean_object* v_snapshot_43_, lean_object* v_r_44_, lean_object* v_k_45_, lean_object* v_demo_46_, lean_object* v___x_47_, lean_object* v___f_48_, lean_object* v___x_49_, lean_object* v_contexts_50_, lean_object* v_inst_51_, lean_object* v_x_52_){
_start:
{
lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___f_56_; 
lean_inc_ref(v___x_49_);
lean_inc(v_x_52_);
v___f_53_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_53_, 0, v_snapshot_43_);
lean_closure_set(v___f_53_, 1, v_x_52_);
lean_closure_set(v___f_53_, 2, v_r_44_);
lean_closure_set(v___f_53_, 3, v_k_45_);
lean_closure_set(v___f_53_, 4, v_demo_46_);
lean_closure_set(v___f_53_, 5, v___x_47_);
lean_closure_set(v___f_53_, 6, v___f_48_);
lean_closure_set(v___f_53_, 7, v___x_49_);
v___x_54_ = lean_apply_1(v_contexts_50_, v_x_52_);
v___x_55_ = lp_mathlib_Finset_sum___redArg(v___x_49_, v_inst_51_, v___f_53_);
lean_dec_ref(v___x_49_);
v___f_56_ = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Basic_Real_Basic_1745762101____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_56_, 0, v___x_54_);
lean_closure_set(v___f_56_, 1, v___x_55_);
return v___f_56_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg(lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_k_59_, lean_object* v_contexts_60_, lean_object* v_demo_61_, lean_object* v_snapshot_62_, lean_object* v_r_63_){
_start:
{
lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___f_67_; lean_object* v___x_68_; 
lean_inc(v_inst_58_);
v___f_64_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_64_, 0, v_inst_58_);
v___x_65_ = lp_mathlib_Real_instAddCommMonoid;
lean_inc(v_k_59_);
v___x_66_ = l_List_finRange(v_k_59_);
v___f_67_ = lean_alloc_closure((void*)(lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg___lam__3), 10, 9);
lean_closure_set(v___f_67_, 0, v_snapshot_62_);
lean_closure_set(v___f_67_, 1, v_r_63_);
lean_closure_set(v___f_67_, 2, v_k_59_);
lean_closure_set(v___f_67_, 3, v_demo_61_);
lean_closure_set(v___f_67_, 4, v___x_66_);
lean_closure_set(v___f_67_, 5, v___f_64_);
lean_closure_set(v___f_67_, 6, v___x_65_);
lean_closure_set(v___f_67_, 7, v_contexts_60_);
lean_closure_set(v___f_67_, 8, v_inst_58_);
v___x_68_ = lp_mathlib_Finset_sum___redArg(v___x_65_, v_inst_57_, v___f_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret(lean_object* v_X_69_, lean_object* v_Y_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_k_73_, lean_object* v_contexts_74_, lean_object* v_demo_75_, lean_object* v_snapshot_76_, lean_object* v_r_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lp_passk_x2dformalization_PassK_Finite_oneStepExpectedRegret___redArg(v_inst_71_, v_inst_72_, v_k_73_, v_contexts_74_, v_demo_75_, v_snapshot_76_, v_r_77_);
return v___x_78_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Values(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_passk_x2dformalization_PassK_OneStepIID(uint8_t builtin) {
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
