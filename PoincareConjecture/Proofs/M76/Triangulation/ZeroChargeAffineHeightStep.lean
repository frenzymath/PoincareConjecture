import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargePairedCapStep
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AffineCylinderExterior
import PoincareConjecture.Proofs.M76.Mathlib.PlanarPLDiskUniqueness












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]




theorem exists_affine_height_coordinates (A : F →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1) (c : ℝ) :
    ∃ f : (E × ℝ) ≃ᴬ[ℝ] F,
      (∀ p, A (f p) = c + p.2) ∧ ∀ y, (f.symm y).2 = A y - c := by
  classical
  let B := A - AffineMap.const ℝ F c
  have hB : B.linear ≠ 0 := by simpa [B] using hA
  obtain ⟨a, R, hleft, hright, ha⟩ := B.exists_zeroLevel_coordinates (F := E) hB hdim
  obtain ⟨v, hv⟩ := (LinearMap.surjective hA) (1 : ℝ)
  have haheight (x : E) : A (a x) = c := by
    have h := ha x
    change A (a x) - c = 0 at h
    linarith
  let g : (E × ℝ) →ᵃ[ℝ] F :=
    a.toAffineMap.comp (LinearMap.fst ℝ E ℝ).toAffineMap +
      ((LinearMap.snd ℝ E ℝ).smulRight v).toAffineMap
  have hg (p : E × ℝ) : g p = a p.1 + p.2 • v := rfl
  have hgheight (p : E × ℝ) : A (g p) = c + p.2 := by
    rw [hg, add_comm (a p.1)]
    change A (p.2 • v +ᵥ a p.1) = c + p.2
    rw [A.map_vadd, map_smul, hv, haheight]
    change p.2 * 1 + c = c + p.2
    ring
  have hginj : Function.Injective g := by
    intro p q hpq
    have ht : p.2 = q.2 := by
      have h := congrArg A hpq
      rw [hgheight, hgheight] at h
      linarith
    have hfirst : a p.1 = a q.1 := by
      rw [hg, hg, ht] at hpq
      exact add_right_cancel hpq
    exact Prod.ext (hleft.injective hfirst) ht
  have hgsurj : Function.Surjective g := by
    intro y
    let t := A y - c
    let z := y - t • v
    have hyz : y - z = t • v := by dsimp [z]; abel
    have hzA : A z = c := by
      have h := A.linearMap_vsub y z
      change A.linear (y - z) = A y - A z at h
      rw [hyz, map_smul, hv] at h
      change t * 1 = A y - A z at h
      dsimp [t] at h
      linarith
    have hzB : z ∈ {x | B x = 0} := by
      change A z - c = 0
      exact sub_eq_zero.mpr hzA
    refine ⟨(R z, t), ?_⟩
    rw [hg, hright hzB]
    exact sub_add_cancel y (t • v)
  let f := (AffineEquiv.ofBijective ⟨hginj, hgsurj⟩).toContinuousAffineEquiv
  have hf (p : E × ℝ) : A (f p) = c + p.2 := hgheight p
  refine ⟨f, hf, ?_⟩
  intro y
  have h := hf (f.symm y)
  rw [f.apply_symm_apply] at h
  linarith





theorem HasPairedHeightCap.affine_image {S C d : Set E} {A : E → ℝ} {a : ℝ}
    (hcap : HasPairedHeightCap S C d A a) (f : E ≃ᴬ[ℝ] F)
    (A' : F → ℝ) (b : ℝ) (hcut : ∀ x, A' (f x) ≤ b ↔ A x ≤ a) :
    HasPairedHeightCap (f '' S) (f '' C) (f '' d) A' b := by
  obtain ⟨B, hB, hBC, hBbelow, hBE⟩ := hcap
  have hsublevel : f '' (S ∩ {x | A x ≤ a}) = (f '' S) ∩ {y | A' y ≤ b} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, (hcut x).mpr hx.2⟩
    · rintro ⟨⟨x, hx, rfl⟩, hxb⟩
      exact ⟨x, ⟨hx, (hcut x).mp hxb⟩, rfl⟩
  have hboundary : f '' (d ∪ (S ∩ {x | A x ≤ a})) =
      (f '' d) ∪ ((f '' S) ∩ {y | A' y ≤ b}) := by
    rw [image_union, hsublevel]
  have hball := hB.affine_image f.toContinuousAffineMap f.injective.injOn
  change IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (f '' B)
    (f '' (d ∪ (S ∩ {x | A x ≤ a}))) at hball
  have hexterior := hBE.affine_cylinderExterior f
  rw [hboundary] at hball hexterior
  refine ⟨f '' B, hball, ?_, ?_, hexterior⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (f.toHomeomorph.image_interior C).subset ⟨x, hBC hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hcut x).mpr (hBbelow hx)




theorem hasPairedHeightCap_affine_height_iff
    (f : (E × ℝ) ≃ᴬ[ℝ] F) (A : F → ℝ) (c t : ℝ)
    (hheight : ∀ p, A (f p) = c + p.2) {S C : Set F} {d : Set (E × ℝ)} :
    HasPairedHeightCap S C (f '' d) A (c + t) ↔
      HasPairedHeightCap (f ⁻¹' S) (f ⁻¹' C) d Prod.snd t := by
  constructor
  · intro h
    have hcut (y : F) : (f.symm y).2 ≤ t ↔ A y ≤ c + t := by
      have hh := hheight (f.symm y)
      rw [f.apply_symm_apply] at hh
      constructor <;> intro hy <;> linarith
    have hback := h.affine_image f.symm Prod.snd t hcut
    simpa only [f.image_symm, f.preimage_image] using hback
  · intro h
    have hcut (p : E × ℝ) : A (f p) ≤ c + t ↔ p.2 ≤ t := by
      rw [hheight]
      exact add_le_add_iff_left c
    have hforward := h.affine_image f A (c + t) hcut
    simpa only [f.image_preimage] using hforward




theorem isFinitePLBallPair_cylinderSlice (K : SimplicialComplex ℝ E) {r t : ℝ}
    (e : (K.space ×ˢ Icc (-r) r : Set (E × ℝ)) ≃ₜ (K.space ×ˢ Icc (-r) r))
    (he : e.IsFinitePL) {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hdK : d ⊆ K.space) (ht : t ∈ Icc (-r) r) :
    IsFinitePLBallPair (ℝ × ℝ) (cylinderSlice e d t) (cylinderSlice e q t) := by
  let D : Set (E × ℝ) := K.space ×ˢ Icc (-r) r
  let i : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E t)
  have hi : Function.Injective i := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  have hdi := hd.affine_image i hi.injOn
  have hdiD : i '' d ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hdK hx, ht⟩
  obtain ⟨g, hg, hge⟩ := he
  have hginj : InjOn g D := by
    intro x hx y hy hxy
    have hsub : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [hge, hge]
      exact hxy
    exact congrArg Subtype.val (e.injective hsub)
  have himage (s : Set E) (hs : s ⊆ K.space) :
      g '' (i '' s) = cylinderSlice e s t := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨(x, t), hs hx, ht⟩, hx, rfl, hge _⟩
    · rintro ⟨p, hp, hpt, rfl⟩
      refine ⟨(p : E × ℝ), ⟨(p : E × ℝ).1, hp, ?_⟩, (hge p).symm⟩
      exact Prod.ext rfl hpt.symm
  have hpair := hdi.image_of_subset hg hdiD hginj
  rwa [himage d hdK, himage q (hd.1.trans hdK)] at hpair





theorem affine_cylinderSlice_eq_disk
    (K : SimplicialComplex ℝ E) {r t c : ℝ}
    (e : (K.space ×ˢ Icc (-r) r : Set (E × ℝ)) ≃ₜ (K.space ×ˢ Icc (-r) r))
    (he : e.IsFinitePL)
    (heheight : ∀ p, (e p : E × ℝ).2 = (p : E × ℝ).2)
    (f : (E × ℝ) ≃ᴬ[ℝ] F) (A : F →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hdim : Module.finrank ℝ F = 3) (hcoord : ∀ p, A (f p) = c + p.2)
    {S actual : Set F} {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hdK : d ⊆ K.space) (ht : t ∈ Icc (-r) r)
    (hsection : ∀ p, f (e p : E × ℝ) ∈ S ↔ (p : E × ℝ).1 ∈ q)
    (hband : S ∩ {y | A y - c ∈ Icc (-r) r} ⊆ f '' (K.space ×ˢ Icc (-r) r))
    (hactual : IsFinitePLBallPair (ℝ × ℝ) actual (S ∩ {y | A y = c + t}))
    (hactualplane : actual ⊆ {y | A y = c + t}) :
    f '' cylinderSlice e d t = actual := by
  have hrim : f '' cylinderSlice e q t = S ∩ {y | A y = c + t} := by
    ext y
    constructor
    · rintro ⟨_, ⟨p, hp, hpt, rfl⟩, rfl⟩
      refine ⟨(hsection p).mpr hp, ?_⟩
      change A (f (e p : E × ℝ)) = c + t
      rw [hcoord, heheight, hpt]
    · intro hy
      have hyband : A y - c ∈ Icc (-r) r := by
        have heq : A y - c = t := by rw [hy.2]; ring
        rw [heq]
        exact ht
      obtain ⟨z, hz, hzy⟩ := hband ⟨hy.1, hyband⟩
      let p := e.symm ⟨z, hz⟩
      have hepy : f (e p : E × ℝ) = y := by
        change f (e (e.symm ⟨z, hz⟩) : E × ℝ) = y
        rw [e.apply_symm_apply]
        exact hzy
      have hpq : (p : E × ℝ).1 ∈ q := (hsection p).mp (hepy.symm ▸ hy.1)
      have hpt : (p : E × ℝ).2 = t := by
        have h := congrArg A hepy
        rw [hcoord, heheight, hy.2] at h
        linarith
      exact ⟨(e p : E × ℝ), ⟨p, hpq, hpt, rfl⟩, hepy⟩
  have hslice := (isFinitePLBallPair_cylinderSlice K e he hd hdK ht).affine_image
    f.toContinuousAffineMap f.injective.injOn
  change IsFinitePLBallPair (ℝ × ℝ) (f '' cylinderSlice e d t)
    (f '' cylinderSlice e q t) at hslice
  rw [hrim] at hslice
  have hplane : f '' cylinderSlice e d t ⊆ {y | A y = c + t} := by
    rintro _ ⟨_, ⟨p, _, hpt, rfl⟩, rfl⟩
    change A (f (e p : E × ℝ)) = c + t
    rw [hcoord, heheight, hpt]
  exact hslice.eq_of_same_rim_in_affine_plane hactual A hA hdim hplane hactualplane






theorem exists_affine_paired_height_cap_step
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hcv : Convex ℝ K.space)
    {r c : ℝ} (hr : 0 < r)
    (e : (K.space ×ˢ Icc (-r) r : Set (E × ℝ)) ≃ₜ (K.space ×ˢ Icc (-r) r))
    (he : e.IsFinitePL)
    (heheight : ∀ p, (e p : E × ℝ).2 = (p : E × ℝ).2)
    (hstart : ∀ p : (K.space ×ˢ Icc (-r) r : Set (E × ℝ)),
      (p : E × ℝ).2 = 0 → e p = p)
    (f : (E × ℝ) ≃ᴬ[ℝ] F) (A : F →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hdim : Module.finrank ℝ F = 3) (hcoord : ∀ p, A (f p) = c + p.2)
    {S C : Set F} {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hdK : d ⊆ interior K.space) (hdC : ∀ x ∈ d, f (x, (0 : ℝ)) ∈ interior C)
    (hsection : ∀ p, f (e p : E × ℝ) ∈ S ↔ (p : E × ℝ).1 ∈ q)
    (hband : S ∩ {y | A y - c ∈ Icc (-r) r} ⊆ f '' (K.space ×ˢ Icc (-r) r))
    (disks : ℝ → Set F)
    (hdisks : ∀ t ∈ Icc (-r) r,
      IsFinitePLBallPair (ℝ × ℝ) (disks (c + t)) (S ∩ {y | A y = c + t}) ∧
        disks (c + t) ⊆ {y | A y = c + t}) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧
      ∀ a b : ℝ, |a - c| ≤ ε → |b - c| ≤ ε → a ≤ b →
        HasPairedHeightCap S C (disks a) A a →
          HasPairedHeightCap S C (disks b) A b := by
  have hdC' : ∀ x ∈ d, (x, (0 : ℝ)) ∈ interior (f ⁻¹' C) := by
    intro x hx
    exact (f.toHomeomorph.preimage_interior C).subset (hdC x hx)
  have hband' : (f ⁻¹' S) ∩ {p | p.2 ∈ Icc (-r) r} ⊆ K.space ×ˢ Icc (-r) r := by
    intro p hp
    have hh : A (f p) - c = p.2 := by rw [hcoord]; ring
    have hfp : f p ∈ S ∩ {y | A y - c ∈ Icc (-r) r} := by
      refine ⟨hp.1, ?_⟩
      change A (f p) - c ∈ Icc (-r) r
      rw [hh]
      exact hp.2
    obtain ⟨z, hz, hzp⟩ := hband hfp
    exact f.injective hzp ▸ hz
  obtain ⟨ε, hε, hεr, hstep⟩ := exists_paired_height_cap_step K hK hcv hr e he
    heheight hstart hd.isCompact hdK hdC' hd.1 hsection hband'
  have hslice (t : ℝ) (ht : t ∈ Icc (-r) r) :
      f '' cylinderSlice e d t = disks (c + t) :=
    affine_cylinderSlice_eq_disk K e he heheight f A hA hdim hcoord hd
      (hdK.trans interior_subset) ht hsection hband (hdisks t ht).1 (hdisks t ht).2
  refine ⟨ε, hε, hεr, ?_⟩
  intro a b ha hb hab hcap
  have haI : a - c ∈ Icc (-r) r := by
    obtain ⟨hal, hau⟩ := abs_le.mp ha
    constructor <;> linarith
  have hbI : b - c ∈ Icc (-r) r := by
    obtain ⟨hbl, hbu⟩ := abs_le.mp hb
    constructor <;> linarith
  have hca : c + (a - c) = a := by ring
  have hcb : c + (b - c) = b := by ring
  have hstart' : HasPairedHeightCap (f ⁻¹' S) (f ⁻¹' C)
      (cylinderSlice e d (a - c)) Prod.snd (a - c) := by
    apply (hasPairedHeightCap_affine_height_iff f A c (a - c) hcoord).mp
    simpa only [hslice (a - c) haI, hca] using hcap
  have hend := hstep (a - c) (b - c) ha hb (sub_le_sub_right hab c) hstart'
  have hback := (hasPairedHeightCap_affine_height_iff f A c (b - c) hcoord).mpr hend
  simpa only [hslice (b - c) hbI, hcb] using hback

end PoincareConjecture.M76.ZeroChargeJoint
