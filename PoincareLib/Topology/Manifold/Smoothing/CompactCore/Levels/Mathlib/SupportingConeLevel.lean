import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Levels.Mathlib.ConeHeightLink
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedSubcomplexCarriers

/-!
# Every supporting-level point lies in the entire cone link

The apex has strictly larger height and all vertices lie above the
supporting level. The exact induced-subcomplex superlevel theorem
removes the apex from every supporting face. This is the lower-level
inclusion in Wall013, section 6, equation (4).
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} {f : E → ℝ}

/-- A supporting-level point of a cone lies in its complete link
when the apex is higher. Other link vertices may also be higher;
the supporting-face argument retains every equality-level point.
See Wall013, equation (4). -/
theorem AffineOnFaces.supporting_level_subset_link (hf : K.AffineOnFaces f)
    (p : E) (r : ℝ) (hstar : K.closedStar p = K) (hp : r < f p)
    (hvertices : ∀ v ∈ K.vertices, r ≤ f v) :
    K.space ∩ {x | f x = r} ⊆ (K.link p).space := by
  have hneg : K.AffineOnFaces (fun x => -f x) :=
    hf.postcomp (-ContinuousAffineMap.id ℝ ℝ)
  have hsuper := hneg.vertexSuperlevel_space (-r) (by
    intro s hs
    apply Or.inl
    intro v hv
    exact neg_le_neg (hvertices v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))))
  have hsub : K.vertexSubcomplex {x | -r ≤ -f x} ≤ K.link p := by
    intro s hs
    have hcone : s ∈ (K.closedStar p).faces := hstar.symm ▸ hs.1
    refine ⟨hs.1, ?_, hcone.2⟩
    intro hps
    have h := hs.2 p hps
    change -r ≤ -f p at h
    linarith
  rintro x ⟨hx, hfx⟩
  apply space_subset_of_le hsub
  rw [hsuper]
  exact ⟨hx, by change -r ≤ -f x; rw [hfx]⟩

end Geometry.SimplicialComplex
