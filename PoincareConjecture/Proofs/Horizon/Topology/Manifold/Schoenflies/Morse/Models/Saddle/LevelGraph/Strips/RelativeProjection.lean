import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Projection



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)


def stripPlaneMap (g : S2 → E3) (v : E3) (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2)
    (F : OpenPartialHomeomorph (Real × Real) S2) (z : Real × Real) : E2 :=
  J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F z)))



theorem projected_strip_interval_family_geometry
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} (hv : ‖v‖ = 1) (F : OpenPartialHomeomorph (Real × Real) S2)
    {l u w c r : Real} (hw : 0 < w) (hrw : r < w)
    (hsource : F.source = Ioo (l - w) (u + w) ×ˢ Ioo (-w) w)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (hheight : ∀ z ∈ F.source, inner Real v (g (F z)) = c + z.2)
    (J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2) (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
    let f : Real × Real → E2 := fun z =>
      Q (J ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (z.2, z.1)))))
    ContDiffOn Real ∞ f (Ioo (-w) w ×ˢ Ioo (l - w) (u + w)) ∧
      (∀ t ∈ Icc (-r) r, InjOn (fun s => f (t, s)) (Icc l u)) ∧
      ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc l u, deriv (fun y => f (t, y)) s ≠ 0 := by
  let q : Real × Real → (Real ∙ v)ᗮ :=
    fun z => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (z.2, z.1)))
  let p : Real × Real → E2 := fun z => J (q z)
  let f : Real × Real → E2 := fun z => Q (p z)
  let W : Set (Real × Real) := Ioo (-w) w ×ˢ Ioo (l - w) (u + w)
  have hq : ContDiffOn Real ∞ q W := by
    apply (contMDiffOn_projected_strip hg v F hF).contDiffOn.comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    intro z hz
    rw [hsource]
    exact ⟨hz.2, hz.1⟩
  have hp : ContDiffOn Real ∞ p W := J.contDiff.contDiffOn.comp hq (mapsTo_univ _ _)
  have hf : ContDiffOn Real ∞ f W := Q.contMDiff.contDiff.contDiffOn.comp hp (mapsTo_univ _ _)
  have hsopen (s : Real) (hs : s ∈ Icc l u) : s ∈ Ioo (l - w) (u + w) :=
    ⟨by linarith only [hw, hs.1], by linarith only [hw, hs.2]⟩
  have htopen (t : Real) (ht : t ∈ Icc (-r) r) : t ∈ Ioo (-w) w :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgeom (t : Real) (ht : t ∈ Icc (-r) r) :=
    projected_strip_slice_geometry hg hv F hsource hF hFi
      (fun s hs t ht => hheight (s, t) (hsource ▸ ⟨hs, ht⟩)) t (htopen t ht)
  refine ⟨hf, ?_, ?_⟩
  · intro t ht s hs y hy heq
    exact (hgeom t ht).2.1 (hsopen s hs) (hsopen y hy) (J.injective (Q.injective heq))
  · intro t ht s hs
    have hqs : DifferentiableAt Real (fun y => q (t, y)) s :=
      ((hgeom t ht).1.contMDiffAt (isOpen_Ioo.mem_nhds (hsopen s hs))).contDiffAt.differentiableAt
        (by simp)
    have hqd : Injective (fderiv Real (fun y => q (t, y)) s) := by
      have hd := (hgeom t ht).2.2 s (hsopen s hs)
      rw [mfderiv_eq_fderiv] at hd
      exact hd
    have hps := J.toContinuousLinearEquiv.hasFDerivAt.comp s hqs.hasFDerivAt
    have hQder : Injective (fderiv Real Q (p (t, s))) := by
      have hh : Injective (mfderiv (𝓡 2) (𝓡 2) Q (p (t, s))) :=
        (Q.mfderivToContinuousLinearEquiv (by simp) _).injective
      rwa [mfderiv_eq_fderiv] at hh
    have hfd := (Q.contMDiff.contDiff.differentiable (by simp) (p (t, s))).hasFDerivAt.comp s hps
    have hfdEq : fderiv Real (fun y => f (t, y)) s =
        (fderiv Real Q (p (t, s))).comp
          (J.toContinuousLinearEquiv.toContinuousLinearMap.comp
            (fderiv Real (fun y => q (t, y)) s)) := hfd.fderiv
    have hi : Injective (fderiv Real (fun y => f (t, y)) s) := by
      rw [hfdEq]
      exact hQder.comp (J.injective.comp hqd)
    intro hz
    have h10 : (1 : Real) = 0 := hi (by simpa only [map_zero, fderiv_apply_one_eq_deriv] using hz)
    exact one_ne_zero h10

end Poincare.Manifold.Schoenflies.SaddleLevel
