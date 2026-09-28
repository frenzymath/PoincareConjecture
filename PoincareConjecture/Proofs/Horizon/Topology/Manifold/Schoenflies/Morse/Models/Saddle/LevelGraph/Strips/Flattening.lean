import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.Cylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates



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
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩




theorem exists_supported_ambient_strip_flattening
    {g : S2 -> E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} (hv : ‖v‖ = 1) (F : OpenPartialHomeomorph (Real × Real) S2)
    {a b w c r R : Real} (hw : 0 < w) (hr : 0 < r) (hrw : r < w) (hrR : r < R)
    (hsource : F.source = Ioo (a - w) (b + w) ×ˢ Ioo (-w) w)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (hheight : ∀ z ∈ F.source, inner Real v (g (F z)) = c + z.2)
    {U : Set (Real ∙ v)ᗮ} (hU : IsOpen U)
    (hproject : ∀ q ∈ F.target, (Real ∙ v)ᗮ.orthogonalProjectionOnto (g q) ∈ U) :
    ∃ K : Set E3, IsCompact K ∧
      K ⊆ {x | |inner Real v x - c| ≤ R ∧
        (Real ∙ v)ᗮ.orthogonalProjectionOnto x ∈ U} ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (D x) = inner Real v x) ∧
        (∀ x, inner Real v x = c -> D x = x) ∧
        (∀ x ∉ K, D x = x) ∧
        ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc a b,
          D (g (F (s, t))) = g (F (s, 0)) + t • v := by
  let J : (Real ∙ v)ᗮ ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by
      intro heq
      simp [heq] at hv)).repr
  let q : Real × Real -> (Real ∙ v)ᗮ :=
    fun z => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (z.2, z.1)))
  let f : Real × Real -> E2 := fun z => J (q z)
  let W : Set (Real × Real) := Ioo (-w) w ×ˢ Ioo (a - w) (b + w)
  have hW : IsOpen W := isOpen_Ioo.prod isOpen_Ioo
  have hswap (z : Real × Real) (hz : z ∈ W) : (z.2, z.1) ∈ F.source := by
    rw [hsource]
    exact ⟨hz.2, hz.1⟩
  have hq : ContDiffOn Real ∞ q W := by
    apply (contMDiffOn_projected_strip hg v F hF).contDiffOn.comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    exact hswap
  have hf : ContDiffOn Real ∞ f W := J.contDiff.contDiffOn.comp hq (mapsTo_univ _ _)
  have hsopen (s : Real) (hs : s ∈ Icc a b) : s ∈ Ioo (a - w) (b + w) :=
    ⟨by linarith only [hw, hs.1], by linarith only [hw, hs.2]⟩
  have htopen (t : Real) (ht : t ∈ Icc (-r) r) : t ∈ Ioo (-w) w :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hrect : Icc (-r) r ×ˢ Icc a b ⊆ W :=
    fun z hz => ⟨htopen z.1 hz.1, hsopen z.2 hz.2⟩
  have hgeom (t : Real) (ht : t ∈ Icc (-r) r) :=
    projected_strip_slice_geometry hg hv F hsource hF hFi
      (fun s hs t ht => hheight (s, t) (hsource ▸ ⟨hs, ht⟩)) t (htopen t ht)
  have hfinj : ∀ t ∈ Icc (-r) r, InjOn (fun s => f (t, s)) (Icc a b) := by
    intro t ht s hs u hu heq
    exact (hgeom t ht).2.1 (hsopen s hs) (hsopen u hu) (J.injective heq)
  have hfder : ∀ t ∈ Icc (-r) r, ∀ s ∈ Icc a b, deriv (fun y => f (t, y)) s ≠ 0 := by
    intro t ht s hs
    have hqs : DifferentiableAt Real (fun y => q (t, y)) s :=
      ((hgeom t ht).1.contMDiffAt (isOpen_Ioo.mem_nhds (hsopen s hs))).contDiffAt.differentiableAt
        (by simp)
    have hqd : Injective (fderiv Real (fun y => q (t, y)) s) := by
      have hd := (hgeom t ht).2.2 s (hsopen s hs)
      rw [mfderiv_eq_fderiv] at hd
      change Injective (fderiv Real (fun y => q (t, y)) s) at hd
      exact hd
    have hfd : fderiv Real (fun y => f (t, y)) s =
        J.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (fderiv Real (fun y => q (t, y)) s) :=
      (J.toContinuousLinearEquiv.hasFDerivAt.comp s hqs.hasFDerivAt).fderiv
    have hi : Injective (fderiv Real (fun y => f (t, y)) s) := by
      rw [hfd]
      exact J.injective.comp hqd
    intro hz
    have h10 : (1 : Real) = 0 := hi (by simpa only [map_zero, fderiv_apply_one_eq_deriv] using hz)
    exact one_ne_zero h10
  obtain ⟨S, hS, hSU, G, hGt, hGzero, hGfix, hG⟩ :=
    exists_supported_interval_cylinder_within hr hrR (J.toHomeomorph.isOpenMap _ hU)
      f hW hrect hf hfinj hfder (by
        intro t ht s hs
        exact mem_image_of_mem J
          (hproject (F (s, t)) (F.map_source (hswap (t, s) (hrect ⟨ht, hs⟩)))))
  let A₀ := ((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans (Poincare.Geometry.Euclidean.heightCoordinates hv)
  let T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toEquiv := Equiv.addRight (c • v)
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  let A := A₀.toDiffeomorph.trans T
  have hA (z : Real × E2) : A z = (c + z.1) • v + (J.symm z.2 : E3) := by
    change z.1 • v + (J.symm z.2 : E3) + c • v = _
    rw [add_smul]
    abel
  have hAh (z : Real × E2) : inner Real v (A z) = c + z.1 := by
    rw [hA]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm z.2).property]
  have hAp (z : Real × E2) : (Real ∙ v)ᗮ.orthogonalProjectionOnto (A z) = J.symm z.2 := by
    rw [hA, map_add, map_smul]
    have hv0 : (Real ∙ v)ᗮ.orthogonalProjectionOnto v = 0 := by
      apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
      simpa only [Submodule.orthogonal_orthogonal] using Submodule.mem_span_singleton_self v
    simp [hv0]
  have hGit (z : Real × E2) : (G.symm z).1 = z.1 := by
    have hh := hGt (G.symm z)
    rw [G.apply_symm_apply] at hh
    exact hh.symm
  have hGizero (x : E2) : G.symm (0, x) = (0, x) := by
    apply G.injective
    change G (G.symm (0, x)) = G (0, x)
    rw [G.apply_symm_apply, hGzero]
  have hGifix (z : Real × E2) (hz : z ∉ closedBall (0 : Real) R ×ˢ S) : G.symm z = z := by
    apply G.injective
    change G (G.symm z) = G z
    rw [G.apply_symm_apply, hGfix z hz]
  have hGi (t : Real) (ht : t ∈ Icc (-r) r) (s : Real) (hs : s ∈ Icc a b) :
      G.symm (t, f (t, s)) = (t, f (0, s)) := by
    apply G.injective
    change G (G.symm (t, f (t, s))) = G (t, f (0, s))
    rw [G.apply_symm_apply, hG t ht s hs]
  let K := A '' (closedBall (0 : Real) R ×ˢ S)
  let D := (A.symm.trans G.symm).trans A
  refine ⟨K, ((isCompact_closedBall 0 R).prod hS).image A.contMDiff.continuous,
    ?_, D, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hAh, add_sub_cancel_left]
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hz.1
    · rw [hAp]
      obtain ⟨y, hy, heq⟩ := hSU hz.2
      change J y = z.2 at heq
      simpa only [← heq, J.symm_apply_apply] using hy
  · intro x
    change inner Real v (A (G.symm (A.symm x))) = inner Real v x
    rw [hAh, hGit, ← hAh, A.apply_symm_apply]
  · intro x hx
    have hz : (A.symm x).1 = 0 := by
      have hh := hAh (A.symm x)
      rw [A.apply_symm_apply, hx] at hh
      linarith
    change A (G.symm (A.symm x)) = x
    have hp : A.symm x = (0, (A.symm x).2) := Prod.ext hz rfl
    rw [hp, hGizero, ← hp, A.apply_symm_apply]
  · intro x hx
    have hnot : A.symm x ∉ closedBall (0 : Real) R ×ˢ S := by
      intro hin
      exact hx ⟨A.symm x, hin, A.apply_symm_apply x⟩
    change A (G.symm (A.symm x)) = x
    rw [hGifix _ hnot, A.apply_symm_apply]
  · intro t ht s hs
    have hdecomp (x : E3) : inner Real v x • v +
        ((Real ∙ v)ᗮ.orthogonalProjectionOnto x : E3) = x :=
      (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply x
    have hAf (t u : Real) : A (t, f (u, s)) =
        (c + t) • v + ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (s, u))) : E3) := by
      rw [hA]
      simp only [f, q, J.symm_apply_apply]
    have hAt : A (t, f (t, s)) = g (F (s, t)) := by
      rw [hAf, ← hheight (s, t) (hswap (t, s) (hrect ⟨ht, hs⟩))]
      exact hdecomp _
    have hAz : c • v + ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (s, 0))) : E3) =
        g (F (s, 0)) := by
      have hz : (s, 0) ∈ F.source := hswap (0, s) (hrect ⟨by constructor <;> linarith, hs⟩)
      have hh : inner Real v (g (F (s, 0))) = c := by simpa using hheight (s, 0) hz
      rw [← hh]
      exact hdecomp _
    rw [← hAt]
    change A (G.symm (A.symm (A (t, f (t, s))))) = _
    rw [A.symm_apply_apply, hGi t ht s hs, hAf, add_smul]
    calc
      _ = (c • v + ((Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (s, 0))) : E3)) + t • v := by abel
      _ = _ := congrArg (fun x => x + t • v) hAz

end Poincare.Manifold.Schoenflies.SaddleLevel
