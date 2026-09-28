import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ExponentialRays










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

private theorem intrinsicEDist_reverse
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (U : Set M) (x y : M) :
    intrinsicEDist g U x y = intrinsicEDist g U y x := by
  suffices h : ∀ x y, intrinsicEDist g U y x ≤ intrinsicEDist g U x y from
    le_antisymm (h y x) (h x y)
  intro x y
  apply le_sInf
  rintro l ⟨γ, hγ, hγ0, hγ1, hγU, rfl⟩
  let r : ℝ → ℝ := fun t => 1 - t
  have hr : MapsTo r (Icc 0 1) (Icc 0 1) := by
    intro t ht
    exact ⟨by dsimp [r]; linarith [ht.2], by dsimp [r]; linarith [ht.1]⟩
  have hrC : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 r := by
    rw [contMDiff_iff_contDiff]
    fun_prop
  have hrev : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (γ ∘ r) (Icc 0 1) :=
    hγ.comp hrC.contMDiffOn hr
  have hlength : g.pathELength (γ ∘ r) 0 1 = g.pathELength γ 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.pathELength (𝓡 3) (γ ∘ r) 0 1 =
      Manifold.pathELength (𝓡 3) γ 0 1
    have hanti : AntitoneOn r (Icc 0 1) := fun _ _ _ _ hab => sub_le_sub_left hab 1
    have hd : DifferentiableOn ℝ r (Icc 0 1) := by
      exact (show Differentiable ℝ r by fun_prop).differentiableOn
    simpa only [r, sub_self, sub_zero] using
      Manifold.pathELength_comp_of_antitoneOn (I := 𝓡 3) (γ := γ)
        (f := r) zero_le_one hanti hd (by
          simpa only [r, sub_self, sub_zero] using hγ.mdifferentiableOn one_ne_zero)
  apply (sInf_le ?_).trans_eq hlength
  exact ⟨γ ∘ r, hrev, by simpa [r] using hγ1, by simpa [r] using hγ0,
    image_subset_iff.mpr (fun t ht => hγU ⟨r t, hr ht, rfl⟩), rfl⟩

private theorem mfderiv_reverse_apply_one
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {γ : ℝ → M} {L t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (L - t)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => γ (L - s)) t 1 =
      -mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ (L - t) 1 := by
  have hr : HasDerivAt (fun s : ℝ => L - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub L
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (γ ∘ fun s => L - s) t 1 = _
  rw [mfderiv_comp_apply t (hγ.mdifferentiableAt (by simp))
    hr.differentiableAt.mdifferentiableAt]
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => L - s) t 1 = -1 := by
    have hd' : fderiv ℝ (fun s : ℝ => L - s) t 1 = -1 := by
      rw [fderiv_eq_smul_deriv, one_smul, hr.deriv]
    erw [mfderiv_eq_fderiv, hd']
  rw [hd]
  exact (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ (L - t)).map_neg 1



theorem long_neck_geodesics_are_almost_axial_signed {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (N : EpsilonNeck g),
        N.epsilon ≤ ε₀ → ∀ {γ : ℝ → M} {L : ℝ},
        N.scale / (100 * N.epsilon) < L →
        g.IsGeodesicOn γ (Icc 0 L) →
        (∀ t ∈ Icc 0 L, γ t ∈ N.carrier) →
        (∀ t ∈ Icc 0 L,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) →
        (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
          a ≤ b → ENNReal.ofReal (b - a) ≤
            intrinsicEDist g N.carrier (γ a) (γ b)) →
        ∀ {σ : ℝ}, |σ| = 1 →
        σ * (N.coordinate_inverse (γ 0)).2 < σ * (N.coordinate_inverse (γ L)).2 →
        ∀ t ∈ Icc 0 L,
        let a : TangentSpace (𝓡 3) (γ t) := N.scale⁻¹ •
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            N.coordinate_map (N.coordinate_inverse (γ t)) (0, 1)
        g.tangentNorm (γ t) (σ • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1 - a) < α := by
  obtain ⟨ε₀, hε₀, haxial⟩ := long_neck_geodesics_are_almost_axial.{u} hα
  refine ⟨ε₀, hε₀, ?_⟩
  intro M _ _ _ _ _ _ _ g N hN γ L hL hγ hcarrier hunit hsegment σ hσ horient t ht
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hσ with rfl | rfl
  · simpa only [one_mul, one_smul] using
      haxial N hN hL hγ hcarrier hunit hsegment (by simpa using horient) t ht
  · let η : ℝ → M := fun s => γ (L - s)
    have hrev (s : ℝ) (hs : s ∈ Icc 0 L) : L - s ∈ Icc 0 L :=
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hη : g.IsGeodesicOn η (Icc 0 L) := by
      intro s hs
      have hmem : (-1 : ℝ) * s + L ∈ Icc 0 L := by
        convert hrev s hs using 1
        ring
      simpa only [neg_one_mul, neg_add_eq_sub] using hγ.comp_affine (-1) L s hmem
    have hηcarrier : ∀ s ∈ Icc 0 L, η s ∈ N.carrier :=
      fun s hs => hcarrier (L - s) (hrev s hs)
    have hd (s : ℝ) (hs : s ∈ Icc 0 L) :
        mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η s 1 =
          -mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ (L - s) 1 :=
      mfderiv_reverse_apply_one (hγ.contMDiffAt (hrev s hs))
    have hηunit : ∀ s ∈ Icc 0 L,
        g.tangentNorm (η s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η s 1) = 1 := by
      intro s hs
      rw [hd s hs]
      simpa only [RiemannianMetric.tangentNorm, map_neg, neg_apply, neg_neg] using
        hunit (L - s) (hrev s hs)
    have hηsegment : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
        a ≤ b → ENNReal.ofReal (b - a) ≤ intrinsicEDist g N.carrier (η a) (η b) := by
      intro a ha b hb hab
      have h := hsegment (L - b) (hrev b hb) (L - a) (hrev a ha) (by linarith)
      rw [intrinsicEDist_reverse] at h
      have heq : L - a - (L - b) = b - a := by ring
      simpa only [η, heq] using h
    have hηorient : (N.coordinate_inverse (η 0)).2 < (N.coordinate_inverse (η L)).2 := by
      dsimp only [η]
      simp only [sub_zero, sub_self]
      simpa only [neg_one_mul, neg_lt_neg_iff] using horient
    have h := haxial N hN hL hη hηcarrier hηunit hηsegment hηorient
      (L - t) (hrev t ht)
    dsimp only at h ⊢
    rw [hd (L - t) (hrev t ht)] at h
    have heq : L - (L - t) = t := by ring
    dsimp only [η] at h
    rw [heq] at h
    simpa only [neg_one_smul] using h

end PoincareConjecture.EpsilonNeck
