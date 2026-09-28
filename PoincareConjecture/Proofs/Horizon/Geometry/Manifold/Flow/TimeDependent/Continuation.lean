import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Local
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Uniqueness








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}


structure SmoothTimeDependentIntegralFamily
    (X : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (V : Set M) (I : Set ℝ) (Φ : ℝ × M → M) : Prop where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (I ×ˢ V)
  orbit : ∀ y ∈ V, ∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => Φ (r, y)) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ (t, y))))

omit [IsManifold (𝓡 n) ∞ M] in
theorem SmoothTimeDependentIntegralFamily.mono
    {V W : Set M} {I J : Set ℝ} {Φ : ℝ × M → M}
    (h : SmoothTimeDependentIntegralFamily X V I Φ) (hW : W ⊆ V) (hJ : J ⊆ I) :
    SmoothTimeDependentIntegralFamily X W J Φ :=
  ⟨h.smooth.mono (prod_mono hJ hW), fun y hy t ht => h.orbit y (hW hy) t (hJ ht)⟩

omit [IsManifold (𝓡 n) ∞ M] in
theorem SmoothTimeDependentIntegralFamily.smooth_orbit
    {V : Set M} {I : Set ℝ} {Φ : ℝ × M → M}
    (h : SmoothTimeDependentIntegralFamily X V I Φ) {y : M} (hy : y ∈ V) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun t => Φ (t, y)) I :=
  h.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ ht => ⟨ht, hy⟩)



theorem SmoothTimeDependentIntegralFamily.glue [T2Space M]
    {J I L : Set ℝ}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) 1
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    (hI : IsOpen I) (hcI : Convex ℝ I) (hIJ : I ⊆ J)
    (hL : IsOpen L) (hcL : Convex ℝ L)
    {V : Set M} (hV : IsOpen V) {s : ℝ} {Φ Ψ : ℝ × M → M}
    (hΦ : SmoothTimeDependentIntegralFamily X V I Φ)
    (hΨ : SmoothTimeDependentIntegralFamily X V L Ψ)
    (hs : s ∈ I ∩ L) (he : ∀ y ∈ V, Φ (s, y) = Ψ (s, y)) :
    ∃ Ξ : ℝ × M → M, SmoothTimeDependentIntegralFamily X V (I ∪ L) Ξ ∧
      EqOn Ξ Φ (I ×ˢ V) ∧ EqOn Ξ Ψ (L ×ˢ V) := by
  classical
  let Ξ : ℝ × M → M := fun p => if p.1 ∈ I then Φ p else Ψ p
  have heΦ : EqOn Ξ Φ (I ×ˢ V) := fun _ hp => if_pos hp.1
  have heΨ : EqOn Ξ Ψ (L ×ˢ V) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    by_cases htI : t ∈ I
    · change (if t ∈ I then Φ (t, y) else Ψ (t, y)) = Ψ (t, y)
      rw [if_pos htI]
      exact timeDependent_integralCurve_eqOn (hI.inter hL)
        (hcI.inter hcL).isPreconnected
        (hX.mono (prod_mono (inter_subset_left.trans hIJ) subset_rfl))
        (fun r hr => hΦ.orbit y hy r hr.1)
        (fun r hr => hΨ.orbit y hy r hr.2) hs (he y hy) ⟨htI, ht⟩
    · exact if_neg htI
  have hlocal {D : Set ℝ} (hD : IsOpen D) {F : ℝ × M → M}
      (hF : SmoothTimeDependentIntegralFamily X V D F)
      (heF : EqOn Ξ F (D ×ˢ V)) :
      SmoothTimeDependentIntegralFamily X V D Ξ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨t, y⟩ ⟨ht, hy⟩
      have hev : Ξ =ᶠ[𝓝 (t, y)] F :=
        Filter.Eventually.mono ((hD.prod hV).mem_nhds ⟨ht, hy⟩) (fun _ hp => heF hp)
      exact ((hF.smooth.contMDiffAt ((hD.prod hV).mem_nhds ⟨ht, hy⟩)).congr_of_eventuallyEq
        hev).contMDiffWithinAt
    · intro y hy t ht
      have hev : (fun r => Ξ (r, y)) =ᶠ[𝓝 t] (fun r => F (r, y)) :=
        Filter.Eventually.mono (hD.mem_nhds ht) (fun r hr => heF ⟨hr, hy⟩)
      have heval : Ξ (t, y) = F (t, y) := heF ⟨ht, hy⟩
      apply ((hF.orbit y hy t ht).congr_of_eventuallyEq hev).congr_mfderiv
      rw [heval]
  have hleft := hlocal hI hΦ heΦ
  have hright := hlocal hL hΨ heΨ
  refine ⟨Ξ, ⟨?_, ?_⟩, heΦ, heΨ⟩
  · rintro ⟨t, y⟩ ⟨ht | ht, hy⟩
    · exact (hleft.smooth.contMDiffAt ((hI.prod hV).mem_nhds ⟨ht, hy⟩)).contMDiffWithinAt
    · exact (hright.smooth.contMDiffAt ((hL.prod hV).mem_nhds ⟨ht, hy⟩)).contMDiffWithinAt
  · intro y hy t ht
    rcases ht with ht | ht
    · exact hleft.orbit y hy t ht
    · exact hright.orbit y hy t ht

omit [IsManifold (𝓡 n) ∞ M] in

theorem SmoothTimeDependentIntegralFamily.restart
    {V W : Set M} {I L : Set ℝ} {s : ℝ} {Φ Ψ : ℝ × M → M}
    (hV : IsOpen V) (hW : IsOpen W) (hI : IsOpen I) (hL : IsOpen L) (hs : s ∈ I)
    (hΦ : SmoothTimeDependentIntegralFamily X V I Φ)
    (hΨ : SmoothTimeDependentIntegralFamily X W L Ψ) :
    IsOpen (V ∩ (fun y => Φ (s, y)) ⁻¹' W) ∧
      SmoothTimeDependentIntegralFamily X (V ∩ (fun y => Φ (s, y)) ⁻¹' W)
        L (fun p => Ψ (p.1, Φ (s, p.2))) := by
  have hslice (y : M) (hy : y ∈ V) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun z => Φ (s, z)) y :=
    (hΦ.smooth.contMDiffAt ((hI.prod hV).mem_nhds ⟨hs, hy⟩)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)
  refine ⟨(show ContinuousOn (fun y => Φ (s, y)) V from
    fun y hy => (hslice y hy).continuousAt.continuousWithinAt).isOpen_inter_preimage hV hW,
    ⟨?_, ?_⟩⟩
  · rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hsecond : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun p : ℝ × M => Φ (s, p.2)) (t, y) :=
      (hΦ.smooth.contMDiffAt ((hI.prod hV).mem_nhds
        (show (s, y) ∈ I ×ˢ V from ⟨hs, hy.1⟩))).comp
          (t, y) (contMDiffAt_const.prodMk contMDiffAt_snd)
    exact ((hΨ.smooth.contMDiffAt ((hL.prod hW).mem_nhds
      (show (t, Φ (s, y)) ∈ L ×ˢ W from ⟨ht, hy.2⟩))).comp
      (t, y) (contMDiffAt_fst.prodMk hsecond)).contMDiffWithinAt
  · exact fun y hy t ht => hΨ.orbit _ hy.2 t ht

end Poincare.Manifold
