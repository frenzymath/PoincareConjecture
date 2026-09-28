import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.EndpointFamily
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.BandFlattening
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open _root_.Poincare.Geometry.Manifold
open Poincare.Geometry.Euclidean

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)
local notation "Itime" => ModelWithCorners.prod 𝓘(Real, Real) (𝓡 1)
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩
private instance : ChartedSpace (E1 × Real) (S1 × Real) := prodChartedSpace E1 S1 Real Real
private instance : ChartedSpace (Real × E1) (Real × S1) := prodChartedSpace Real Real E1 S1

private theorem projected_annulus_slice_embedding
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (F : OpenPartialHomeomorph (S1 × Real) S2) {l u : Real}
    (hsource : F.source = univ ×ˢ Ioo l u)
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo l u → inner Real v (f (F (q, t))) = t)
    (t : Real) (ht : t ∈ Ioo l u) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun q => J ((Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, t))))) := by
  let P : PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ :=
    { toPartialEquiv := F.toPartialEquiv
      open_source := F.open_source
      open_target := F.open_target
      contMDiffOn_toFun := hF
      contMDiffOn_invFun := hFi }
  have hqt (q : S1) : (q, t) ∈ F.source := by rw [hsource]; exact ⟨mem_univ _, ht⟩
  let j : S1 → S2 := fun q => F (q, t)
  have hj : ContMDiff (𝓡 1) (𝓡 2) ∞ j := by
    intro q
    exact (hF.contMDiffAt (F.open_source.mem_nhds (hqt q))).comp q
      ((contMDiff_id.prodMk contMDiff_const) q)
  have hjinj : Injective j := by
    intro q q' heq
    exact congrArg Prod.fst (F.injOn (hqt q) (hqt q') heq)
  have hjder (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 2) j q) := by
    have hpair : MDifferentiableAt (𝓡 1) Iprod (fun q : S1 => (q, t)) q :=
      ((contMDiff_id (n := ∞)).prodMk (contMDiff_const (c := t)) q).mdifferentiableAt (by simp)
    have hloc : IsLocalDiffeomorphAt Iprod (𝓡 2) ∞ F (q, t) :=
      P.isLocalDiffeomorphAt Iprod (𝓡 2) ∞ (hqt q)
    change Injective (mfderiv (𝓡 1) (𝓡 2) (F ∘ fun q : S1 => (q, t)) q)
    rw [mfderiv_comp q (hloc.contMDiffAt.mdifferentiableAt (by simp)) hpair]
    apply (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    change Injective (mfderiv (𝓡 1) Iprod
      (fun q : S1 => (id q, (fun _ : S1 => t) q)) q)
    rw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const,
      mfderiv_id, mfderiv_const]
    exact fun _ _ heq => congrArg Prod.fst heq
  have hfj := hf.contMDiff.comp hj
  have hfjheight (q : S1) : inner Real v ((f ∘ j) q) = t := hheight q t ht
  have hfjder (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) (f ∘ j) q) := by
    rw [mfderiv_comp q (hf.contMDiff.mdifferentiable (by simp) (j q))
      (hj.mdifferentiable (by simp) q)]
    exact (injective_mfderiv_sphere_embedding hf (j q)).comp (hjder q)
  let k : S1 → Hemisphere.Plane v :=
    fun q => (Hemisphere.Plane v).orthogonalProjectionOnto ((f ∘ j) q)
  have hk : ContMDiff (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ k :=
    (Hemisphere.Plane v).orthogonalProjectionOnto.contMDiff.comp hfj
  have hkinj := injective_projection_of_height_eq hv hfjheight (hf.isEmbedding.injective.comp hjinj)
  have hkder := injective_mfderiv_projection_of_height_eq hv hfj hfjheight hfjder
  let L := J.toContinuousLinearEquiv.toDiffeomorph
  apply isSmoothEmbedding_of_injective_mfderiv (L.contMDiff.comp hk) (J.injective.comp hkinj)
  intro q
  change Injective (mfderiv (𝓡 1) (𝓡 2) (L ∘ k) q)
  rw [mfderiv_comp q (L.contMDiff.mdifferentiable (by simp) _) (hk.mdifferentiable (by simp) _)]
  exact (L.mfderivToContinuousLinearEquiv (by simp) (k q)).injective.comp (hkder q)

theorem exists_actual_band_flattening_with_constant_ends
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) {a b δ w : Real}
    (hδ : 0 < δ) (hw : 0 < w) (hsep : a + w < b - w)
    (F : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : F.source = univ ×ˢ Ioo (a - δ) (b + δ))
    (hF : ContMDiffOn Iprod (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target)
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) → inner Real v (f (F (q, t))) = t)
    (hleft : ∀ t ∈ Icc a (a + w),
      range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, t)))) =
        range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, a)))))
    (hright : ∀ t ∈ Icc (b - w) b,
      range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, t)))) =
        range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, b))))) :
    ∃ Q : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
        (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      Q '' range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, b)))) =
        range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, a)))) ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (D x) = inner Real v x) ∧
        (∀ x, inner Real v x ≤ a + w / 4 → D x = x) ∧
        (∀ (t : Real) (x : Hemisphere.Plane v), b - w / 4 ≤ t →
          D (t • v + (x : E3)) = t • v + (Q x : E3)) ∧
        (∀ t ∈ Icc a b, D '' range (fun q => f (F (q, t))) =
          (fun x : Hemisphere.Plane v => t • v + (x : E3)) ''
            range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, a))))) ∧
        D '' (f '' (F '' (univ ×ˢ Icc a b))) =
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc a b ×ˢ range (fun q =>
              (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, a))))) := by
  have hab : a ≤ b := by linarith
  have hinterval {t : Real} (ht : t ∈ Icc a b) : t ∈ Ioo (a - δ) (b + δ) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨κ, hκ, hκrange, hκleft, hκright, hκpieces⟩ :=
    exists_smooth_band_endpoint_clamp hw hsep
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro heq; simp [heq] at hv)).repr
  let C : Real → Set (Hemisphere.Plane v) :=
    fun t => range (fun q => (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, t))))
  let γ : Real × S1 → E2 := fun z =>
    J ((Hemisphere.Plane v).orthogonalProjectionOnto (f (F (z.2, κ z.1))))
  have hmap : ContMDiff Itime Iprod ∞ (fun z : Real × S1 => (z.2, κ z.1)) :=
    contMDiff_snd.prodMk (hκ.contMDiff.comp contMDiff_fst)
  have hFt : ContMDiff Itime (𝓡 2) ∞ (fun z : Real × S1 => F (z.2, κ z.1)) := by
    intro z
    have hz : (z.2, κ z.1) ∈ F.source := by
      rw [hsource]
      exact ⟨mem_univ _, hinterval (hκrange z.1)⟩
    exact (hF.contMDiffAt (F.open_source.mem_nhds hz)).comp z (hmap z)
  have hγ : ContMDiff Itime (𝓡 2) ∞ γ :=
    J.toContinuousLinearEquiv.contDiff.contMDiff.comp
      ((Hemisphere.Plane v).orthogonalProjectionOnto.contMDiff.comp (hf.contMDiff.comp hFt))
  have hemb (t : Real) : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun q => γ (t, q)) :=
    projected_annulus_slice_embedding hf hv J F hsource hF hFi hheight _ (hinterval (hκrange t))
  have hγimage (t : Real) (ht : t ∈ Icc a b) : range (fun q => γ (t, q)) = J '' C t := by
    have heq : C (κ t) = C t := by
      rcases hκpieces t ht with ⟨htl, hκl⟩ | ⟨htr, hκr⟩ | hκt
      · exact (hleft _ hκl).trans (hleft _ htl).symm
      · exact (hright _ hκr).trans (hright _ htr).symm
      · rw [hκt]
    change range (J ∘ fun q =>
      (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, κ t)))) = _
    rw [range_comp, show range (fun q =>
      (Hemisphere.Plane v).orthogonalProjectionOnto (f (F (q, κ t)))) = C (κ t) from rfl, heq]
  obtain ⟨Q₂, hQ₂, _, _, D₂, hD₂height, hD₂lower, hD₂upper, _, hD₂slices, _⟩ :=
    exists_circle_family_flattening_with_constant_ends hw hsep γ hγ (fun t _ => hemb t)
      (fun t ht => by rw [hγimage t ⟨ht.1, by linarith [ht.2]⟩,
        hγimage a ⟨le_rfl, hab⟩, show C t = C a from hleft t ht])
      (fun t ht => by rw [hγimage t ⟨by linarith [ht.1], ht.2⟩,
        hγimage b ⟨hab, le_rfl⟩, show C t = C b from hright t ht])
  let j := J.toContinuousLinearEquiv.toDiffeomorph
  let Q := (j.trans Q₂).trans j.symm
  have hQ : Q '' C b = C a := by
    change (J.symm ∘ Q₂ ∘ J) '' C b = C a
    rw [image_comp, image_comp, ← hγimage b ⟨hab, le_rfl⟩, hQ₂,
      hγimage a ⟨le_rfl, hab⟩, ← image_comp]
    simp only [Function.comp_def, J.symm_apply_apply, image_id']
  let L := (((ContinuousLinearEquiv.refl Real Real).prodCongr
    J.symm.toContinuousLinearEquiv).trans (heightCoordinates hv)).toDiffeomorph
  have hL (z : Real × E2) : L z = z.1 • v + (J.symm z.2 : E3) := rfl
  have hLheight (z : Real × E2) : inner Real v (L z) = z.1 := by
    rw [hL]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J.symm z.2).property]
  have hLi (x : E3) : L.symm x =
      (inner Real v x, J ((Hemisphere.Plane v).orthogonalProjectionOnto x)) := rfl
  have hLplane (t : Real) (x : Hemisphere.Plane v) : L (t, J x) = t • v + (x : E3) := by
    rw [hL, J.symm_apply_apply]
  let D := (L.symm.trans D₂).trans L
  have hcoords (t : Real) (ht : t ∈ Icc a b) :
      L.symm '' range (fun q => f (F (q, t))) = {t} ×ˢ range (fun q => γ (t, q)) := by
    rw [hγimage t ht]
    ext z
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      rw [hLi]
      exact ⟨hheight q t (hinterval ht), ⟨_, mem_range_self q, rfl⟩⟩
    · rintro ⟨hz, _, ⟨q, rfl⟩, hq⟩
      refine ⟨f (F (q, t)), mem_range_self q, ?_⟩
      rw [hLi, hheight q t (hinterval ht)]
      exact Prod.ext hz.symm hq
  have hDslices (t : Real) (ht : t ∈ Icc a b) :
      D '' range (fun q => f (F (q, t))) =
        (fun x : Hemisphere.Plane v => t • v + (x : E3)) '' C a := by
    calc
      D '' range (fun q => f (F (q, t))) =
          L '' (D₂ '' (L.symm '' range (fun q => f (F (q, t))))) := by
        rw [← image_comp, ← image_comp]
        rfl
      _ = L '' ({t} ×ˢ (J '' C a)) := by
        rw [hcoords t ht, hD₂slices t ht, hγimage a ⟨le_rfl, hab⟩]
      _ = _ := by
        ext y
        constructor
        · rintro ⟨⟨u, z⟩, ⟨hu, x, hx, rfl⟩, rfl⟩
          have hut : u = t := hu
          subst u
          exact ⟨x, hx, (hLplane t x).symm⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨(t, J x), ⟨rfl, mem_image_of_mem J hx⟩, hLplane t x⟩
  refine ⟨Q, hQ, D, ?_, ?_, ?_, hDslices, ?_⟩
  · intro x
    change inner Real v (L (D₂ (L.symm x))) = inner Real v x
    rw [hLheight, hD₂height, hLi]
  · intro x hx
    change L (D₂ (L.symm x)) = x
    rw [hLi, hD₂lower _ _ hx]
    exact L.apply_symm_apply x
  · intro t x ht
    rw [← hLplane t x]
    change L (D₂ (L.symm (L (t, J x)))) = _
    rw [L.symm_apply_apply, hD₂upper t (J x) ht, hL]
    rfl
  · ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩, rfl⟩
      obtain ⟨x, hx, hxy⟩ := (hDslices t ht) ▸
        mem_image_of_mem D (mem_range_self q)
      exact ⟨(t, x), ⟨ht, hx⟩, hxy⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      obtain ⟨z, ⟨q, rfl⟩, hq⟩ := (hDslices t ht).symm ▸
        mem_image_of_mem (fun x : Hemisphere.Plane v => t • v + (x : E3)) hx
      exact ⟨f (F (q, t)), ⟨F (q, t), ⟨(q, t), ⟨mem_univ _, ht⟩, rfl⟩, rfl⟩, hq⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
