import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E]

theorem strictMono_vertical_of_compact_support
    (F : E × Real ≃ₜ E × Real)
    (hfirst : ∀ p, (F p).1 = p.1)
    {K : Set (E × Real)} (hK : IsCompact K)
    (hfix : ∀ p ∉ K, F p = p) (x : E) :
    StrictMono (fun z : Real => (F (x, z)).2) := by
  have hc : Continuous (fun z : Real => (F (x, z)).2) :=
    continuous_snd.comp (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hi : Function.Injective (fun z : Real => (F (x, z)).2) := by
    intro a b hab
    have he : F (x, a) = F (x, b) := Prod.ext (by simp only [hfirst]) hab
    exact congrArg Prod.snd (F.injective he)
  rcases hc.strictMono_of_inj hi with hm | ha
  · exact hm
  · obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hout (z : Real) (hz : R < z) : (x, z) ∉ K := by
      intro hp
      have hn := (norm_snd_le (x, z)).trans (hR _ hp)
      have hl : z ≤ ‖z‖ := le_abs_self z
      linarith
    have ha' := ha (show R + 1 < R + 2 by linarith)
    change (F (x, R + 2)).2 < (F (x, R + 1)).2 at ha'
    rw [hfix _ (hout (R + 2) (by linarith)),
      hfix _ (hout (R + 1) (by linarith))] at ha'
    simp only at ha'
    linarith

theorem image_lowerHalfSpace_eq_subgraph
    (F : E × Real ≃ₜ E × Real)
    (hfirst : ∀ p, (F p).1 = p.1)
    {K : Set (E × Real)} (hK : IsCompact K)
    (hfix : ∀ p ∉ K, F p = p)
    (b : E -> Real) (hzero : ∀ x, F (x, 0) = (x, b x)) :
    F '' {p : E × Real | p.2 ≤ 0} = {p | p.2 ≤ b p.1} := by
  ext p
  constructor
  · rintro ⟨⟨x, z⟩, hz, rfl⟩
    change (F (x, z)).2 ≤ b (F (x, z)).1
    rw [hfirst]
    have hm := (strictMono_vertical_of_compact_support F hfirst hK hfix x).monotone hz
    simpa only [hzero] using hm
  · intro hp
    obtain ⟨q, rfl⟩ := F.surjective p
    refine ⟨q, ?_, rfl⟩
    change q.2 ≤ 0
    apply (strictMono_vertical_of_compact_support F hfirst hK hfix q.1).le_iff_le.mp
    simpa only [Set.mem_ofPred_eq, hzero, hfirst, Prod.eta] using hp

end Poincare.Manifold.Schoenflies
