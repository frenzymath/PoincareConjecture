import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]
  {J : Type*} {l : Filter J}

local notation "X" => EuclideanSpace ℝ (Fin d)

theorem m64MemLp_add_tendsto {u : X → E} (hu : MemLp u 2 volume)
    {h : J → X} {a : X} (hh : Tendsto h l (𝓝 a)) :
    Tendsto (fun j => eLpNorm (fun x => u (x + h j) - u (x + a)) 2 volume)
      l (𝓝 0) := by
  let shift : C(X, C(X, X)) :=
    (⟨fun p : X × X => p.2 + p.1, continuous_snd.add continuous_fst⟩ : C(X × X, X)).curry
  have hc : Continuous (fun v : X =>
      Lp.compMeasurePreserving (fun x => x + v)
        (measurePreserving_add_right volume v) (hu.toLp u)) :=
    continuous_const.compMeasurePreservingLp shift.continuous
      (fun v => measurePreserving_add_right volume v) (by norm_num)
  have hlim := (hc.tendsto a).comp hh
  have hmem (v : X) : MemLp (fun x => u (x + v)) 2 volume :=
    hu.comp_measurePreserving (measurePreserving_add_right volume v)
  have heq (v : X) : Lp.compMeasurePreserving (fun x => x + v)
      (measurePreserving_add_right volume v) (hu.toLp u) =
        (hmem v).toLp (fun x => u (x + v)) :=
    Lp.toLp_compMeasurePreserving hu (measurePreserving_add_right volume v)
  simp_rw [heq] at hlim
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j x => u (x + h j)) (fun j => hmem (h j))
    (fun x => u (x + a)) (hmem a)).mp hlim

theorem m64MemLp_add_restrict_tendsto {O K : Set X}
    (hO : MeasurableSet O) (hK : MeasurableSet K)
    {u : X → E} (hu : MemLp u 2 (volume.restrict O))
    {h : J → X} {a : X} (hh : Tendsto h l (𝓝 a))
    (hbase : ∀ᵐ x ∂volume.restrict K, x + a ∈ O)
    (hshift : ∀ j, MapsTo (fun x => x + h j) K O) :
    Tendsto (fun j => eLpNorm (fun x => u (x + h j) - u (x + a))
      2 (volume.restrict K)) l (𝓝 0) := by
  classical
  let U := O.indicator u
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hO).mpr hu
  have hlim := m64MemLp_add_tendsto hU hh
  have hb (j : J) :
      eLpNorm (fun x => u (x + h j) - u (x + a)) 2 (volume.restrict K) ≤
        eLpNorm (fun x => U (x + h j) - U (x + a)) 2 volume := by
    calc
      _ = eLpNorm (fun x => U (x + h j) - U (x + a)) 2 (volume.restrict K) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hK, hbase] with x hx ha
        simp only [U, indicator_of_mem (hshift j hx), indicator_of_mem ha]
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hb

end PoincareConjecture
