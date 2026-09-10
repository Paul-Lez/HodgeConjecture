// Lean compiler output
// Module: KirovDolbeault.Dolbeault.SchwartzFiniteness
// Imports: public import Init public meta import Init public import Mathlib.Analysis.Normed.Operator.Compact.Basic public import Mathlib.Analysis.Normed.Operator.Banach public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative public import Mathlib.Analysis.Normed.Module.RieszLemma public import Mathlib.Analysis.Normed.Module.FiniteDimension public import Mathlib.Analysis.Normed.Group.Quotient public import Mathlib.Analysis.SpecificLimits.Normed public import Mathlib.Analysis.Complex.Basic public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Operator_Compact_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Operator_Banach(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Operator_Compact_FredholmAlternative(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_RieszLemma(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_FiniteDimension(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Group_Quotient(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecificLimits_Normed(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_FiniteDimensional_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PortTest_KirovDolbeault_Dolbeault_SchwartzFiniteness(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Operator_Compact_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Operator_Banach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Operator_Compact_FredholmAlternative(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Module_RieszLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Module_FiniteDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Group_Quotient(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecificLimits_Normed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_FiniteDimensional_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
