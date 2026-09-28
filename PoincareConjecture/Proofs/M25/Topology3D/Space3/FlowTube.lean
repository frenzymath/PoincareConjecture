import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set
open scoped ContDiff Manifold NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (V : ℝ × E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)
variable (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V) (s : ℝ)

noncomputable def clockGraphDiffeomorph :
    Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ where
  toEquiv := {
    toFun := fun p => (clockEvolution V hK hL s p.2 p.1, p.2)
    invFun := fun p => (clockEvolution V hK hL p.2 s p.1, p.2)
    left_inv := fun p => Prod.ext (clockEvolution_reverse V hK hL s p.2 p.1) rfl
    right_inv := fun p => Prod.ext (clockEvolution_reverse V hK hL p.2 s p.1) rfl }
  contMDiff_toFun := by
    exact (((clockEvolution_contDiff V hK hL hV hs).comp
      (((contDiff_const (c := s)).prodMk contDiff_snd).prodMk contDiff_fst)).prodMk
      contDiff_snd).contMDiff
  contMDiff_invFun := by
    exact (((clockEvolution_contDiff V hK hL hV hs).comp
      ((contDiff_snd.prodMk (contDiff_const (c := s))).prodMk contDiff_fst)).prodMk
      contDiff_snd).contMDiff

@[simp] theorem clockGraphDiffeomorph_apply (p : E × ℝ) :
    clockGraphDiffeomorph V hK hL hV hs s p =
      (clockEvolution V hK hL s p.2 p.1, p.2) := rfl

@[simp] theorem clockGraphDiffeomorph_symm_apply (p : E × ℝ) :
    (clockGraphDiffeomorph V hK hL hV hs s).symm p =
      (clockEvolution V hK hL p.2 s p.1, p.2) := rfl

noncomputable def flowTubeChart (e : OpenPartialHomeomorph E E) :
    OpenPartialHomeomorph (E × ℝ) (E × ℝ) :=
  (e.prod (OpenPartialHomeomorph.refl ℝ)).trans
    (clockGraphDiffeomorph V hK hL hV hs s).toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem flowTubeChart_apply (e : OpenPartialHomeomorph E E) (p : E × ℝ) :
    flowTubeChart V hK hL hV hs s e p =
      (clockEvolution V hK hL s p.2 (e p.1), p.2) := rfl

@[simp] theorem flowTubeChart_source (e : OpenPartialHomeomorph E E) :
    (flowTubeChart V hK hL hV hs s e).source = e.source ×ˢ (univ : Set ℝ) := by
  ext p
  simp [flowTubeChart]

@[simp] theorem flowTubeChart_symm_apply (e : OpenPartialHomeomorph E E) (p : E × ℝ) :
    (flowTubeChart V hK hL hV hs s e).symm p =
      (e.symm (clockEvolution V hK hL p.2 s p.1), p.2) := rfl

theorem flowTubeChart_contDiffOn (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) :
    ContDiffOn ℝ ∞ (flowTubeChart V hK hL hV hs s e)
      (flowTubeChart V hK hL hV hs s e).source := by
  rw [flowTubeChart_source]
  exact (clockGraphDiffeomorph V hK hL hV hs s).contMDiff_toFun.contDiff.comp_contDiffOn
    (he.prodMap contDiff_id.contDiffOn)

theorem flowTubeChart_symm_contDiffOn (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (flowTubeChart V hK hL hV hs s e).symm
      (flowTubeChart V hK hL hV hs s e).target := by
  exact (he.prodMap contDiff_id.contDiffOn).comp
    (clockGraphDiffeomorph V hK hL hV hs s).contMDiff_invFun.contDiff.contDiffOn
    (fun p hp => hp.2)

theorem flowTubeChart_boundary {Q : Type*} (e : OpenPartialHomeomorph E E)
    (r : Q → E) (c : ℝ → Q → E) {a b : ℝ} (hbase : s ∈ Ioo a b)
    (he : ∀ q, e (r q) = c s q)
    (hc : ∀ q t, t ∈ Ioo a b → HasDerivAt (fun z => c z q) (V (t, c t q)) t)
    (q : Q) {z : ℝ} (hz : z ∈ Ioo a b) :
    flowTubeChart V hK hL hV hs s e (r q, z) = (c z q, z) := by
  rw [flowTubeChart_apply, he q]
  exact Prod.ext (clockEvolution_tracks V hK hL (fun t => c t q) hbase (hc q) hz) rfl

end PoincareConjecture.M25.Topology3D
