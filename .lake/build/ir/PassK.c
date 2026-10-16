// Lean compiler output
// Module: PassK
// Imports: public import Init public meta import Init public import PassK.Values public import PassK.Definitions public import PassK.Coverage public import PassK.GreedyCoverage public import PassK.Bounds public import PassK.Preliminaries public import PassK.OnlineRegret public import PassK.PolicyMixture public import PassK.OneStepIID public import PassK.FiniteTail public import PassK.MomentToTail public import PassK.StandardRobustPAC public import PassK.FiniteTesting public import PassK.TwoPoint public import PassK.LowerBounds public import PassK.UpperBounds public import PassK.Stage1LogPotential public import PassK.Stage1LogUpdates public import PassK.Stage2Exponential public import PassK.Stage3Rates public import PassK.Stage4LeCam public import PassK.Stage5Minimax
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Values(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Definitions(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Coverage(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_GreedyCoverage(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Bounds(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Preliminaries(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_OnlineRegret(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_PolicyMixture(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_OneStepIID(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_FiniteTail(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_MomentToTail(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_StandardRobustPAC(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_FiniteTesting(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_TwoPoint(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_LowerBounds(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_UpperBounds(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Stage1LogPotential(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Stage1LogUpdates(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Stage2Exponential(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Stage3Rates(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Stage4LeCam(uint8_t builtin);
lean_object* initialize_passk_x2dformalization_PassK_Stage5Minimax(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_passk_x2dformalization_PassK(uint8_t builtin) {
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
res = initialize_passk_x2dformalization_PassK_Definitions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Coverage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_GreedyCoverage(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Bounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Preliminaries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_OnlineRegret(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_PolicyMixture(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_OneStepIID(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_FiniteTail(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_MomentToTail(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_StandardRobustPAC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_FiniteTesting(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_TwoPoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_LowerBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_UpperBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Stage1LogPotential(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Stage1LogUpdates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Stage2Exponential(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Stage3Rates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Stage4LeCam(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_passk_x2dformalization_PassK_Stage5Minimax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
