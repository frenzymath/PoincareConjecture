import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SphereModelCap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SeparatedSphereCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Metric Geometry Geometry.SeparatedSphereCaps

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_domain_capped_complex
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (B : κ → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBR : ∀ i, B i ⊆ frontier R)
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (K L : SimplicialComplex ℝ (t → ℝ × V3)) (H : R ≃ₜ K.space)
      (C : SimplicialComplex ℝ ((t → ℝ × V3) × (κ → ℝ))),
      Continuous F ∧
      (∀ j, LocallyPiecewiseAffineOn (F ∘ (e j).symm) (e j).target) ∧
      InjOn F R ∧ K.faces.Finite ∧ L ≤ K ∧ L.faces.Finite ∧
      K.space = F '' R ∧ L.space = F '' frontier R ∧
      (∀ x : R, (H x : t → ℝ × V3) = F x) ∧
      (∀ z : K.space, F (H.symm z) = (z : t → ℝ × V3)) ∧
      (∀ x : R, (H x : t → ℝ × V3) ∈ L.space ↔ (x : X) ∈ frontier R) ∧
      (∀ x ∈ R, ∃ (j : ι) (V : Set X) (a : (t → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e j).source ∧ EqOn (a ∘ F) (e j) V) ∧
      (∀ i, F '' B i ⊆ L.space) ∧
      (∀ i, ∃ Q : B i ≃ₜ (lift '' (F '' B i) : Set ((t → ℝ × V3) × (κ → ℝ))),
        ∀ x : B i, (Q x : (t → ℝ × V3) × (κ → ℝ)) = lift (F x)) ∧
      (∀ i, IsFinitePLBallPair V3 (cap i (F '' B i)) (lift '' (F '' B i))) ∧
      (∀ i, cap i (F '' B i) ∩ lift '' K.space = lift '' (F '' B i)) ∧
      Pairwise (fun i j => Disjoint (cap i (F '' B i)) (cap j (F '' B j))) ∧
      C.faces.Finite ∧ C.space = lift '' K.space ∪ ⋃ i, cap i (F '' B i) := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨t, F, K, L, H, hFc, hF, hK, hLK, hL, hKs, hLs, hHF, hbound, hproj⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      e he.compatible he.cover hR he.halfspace
  have hFinj : InjOn F R := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))))
  have hBiR (i : κ) : B i ⊆ R := (hBR i).trans hR.isClosed.frontier_subset
  have hBSK (i : κ) : F '' B i ⊆ K.space := by
    rw [hKs]
    exact image_mono (hBiR i)
  have himageDis : Pairwise (fun i j => Disjoint (F '' B i) (F '' B j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x, hx, hFx⟩ ⟨y, hy, hFy⟩
    have hxy : x = y := hFinj (hBiR i hx) (hBiR j hy) (hFx.trans hFy.symm)
    exact disjoint_left.mp (hdis hij) hx (hxy ▸ hy)
  have hparam (i : κ) := (sB i).exists_finitePL_model_parametrization
    F hF (hFinj.mono (hBiR i)) rfl
  choose P hP hPval using hparam
  have hfront : sphere (0 : V3) 1 = frontier (closedBall (0 : V3) 1) :=
    (frontier_closedBall _ one_ne_zero).symm
  let D (i : κ) := (P i).symm.trans (Homeomorph.setCongr hfront)
  have hD (i : κ) : (D i).IsFinitePL := (hP i).symm.setCongr rfl hfront
  have hne (i : κ) : (F '' B i).Nonempty := by
    obtain ⟨x, hx⟩ := (show (sphere (0 : V3) 1).Nonempty from
      NormedSpace.sphere_nonempty.mpr zero_le_one)
    exact ⟨P i ⟨x, hx⟩, (P i ⟨x, hx⟩).property⟩
  obtain ⟨hball, hinter, hcapDis, C, hC, hCs⟩ :=
    exists_finite_capped_complex K hK (fun i => F '' B i) hBSK himageDis
      D hD hne (isCompact_closedBall _ _) (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
  refine ⟨t, F, K, L, H, C, hFc, hF, hFinj, hK, hLK, hL, hKs, hLs,
    hHF, ?_, hbound, hproj, ?_, ?_, hball, hinter, hcapDis, hC, hCs⟩
  · intro z
    rw [← hHF, H.apply_symm_apply]
  · intro i
    rw [hLs]
    exact image_mono (hBR i)
  · intro i
    let : CompactSpace (B i) := isCompact_iff_compactSpace.mp (sB i).isCompact
    let f : X → (t → ℝ × V3) × (κ → ℝ) := fun x => lift (F x)
    have hfc : Continuous f := hFc.prodMk continuous_const
    have hfi : InjOn f (B i) := by
      intro x hx y hy hxy
      exact hFinj (hBiR i hx) (hBiR i hy) (congrArg Prod.fst hxy)
    let Q0 : B i ≃ₜ f '' B i := Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn f (B i) hfi)
      ((hfc.comp continuous_subtype_val).subtype_mk _)
    have himage : f '' B i = lift '' (F '' B i) := (image_image lift F (B i)).symm
    exact ⟨Q0.trans (Homeomorph.setCongr himage), fun _ => rfl⟩

end PoincareConjecture.M76
