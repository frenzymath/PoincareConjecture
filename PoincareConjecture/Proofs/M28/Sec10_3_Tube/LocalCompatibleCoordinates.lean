import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalCenteredTransition












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



private theorem compatible_neck_cut_charts_of_transition
    (A B : EpsilonNeck g)
    (s : ℝ) (hs : s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹)
    (f : UnitTwoSphere → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hfd : ∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹)
    (G : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞)
    (R : ℝ) (hR : 0 < R)
    (hGside : ∀ p : RoundCylinderSpace, (G p).2 ≤ 0 ↔ p.2 ≤ 0)
    (hGzero : ∀ p : RoundCylinderSpace, (G p).2 = 0 ↔ p.2 = 0)
    (hGmap : ∀ (q : UnitTwoSphere) (t : ℝ), |t| < R →
      A.coordinate_map ((G (q, t)).1, f (G (q, t)).1 + (G (q, t)).2) =
        B.coordinate_map (q, s + t)) :
    ∃ (r : ℝ)
      (DA : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞)
      (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace B.carrierOpen ∞),
      0 < r ∧
      (∀ p, (A.coordinate_inverse (DA p)).1 = p.1) ∧
      (∀ q, A.coordinate_inverse (DA (q, 0)) = (q, f q)) ∧
      (∀ p, (A.coordinate_inverse (DA p)).2 ≤ f p.1 ↔ p.2 ≤ 0) ∧
      (∀ p, s < (B.coordinate_inverse (T p)).2 ↔ 0 < p.2) ∧
      (∀ p, |p.2| < r → (DA p : M) = T p) := by
  obtain ⟨rA, DA, hrA, hDAangle, hDAaff, hDAside⟩ :=
    A.exists_affine_neck_coordinates f hf hfd
  obtain ⟨rB, DB, hrB, hDBangle, hDBaff, hDBside⟩ :=
    B.exists_affine_neck_coordinates (fun _ => s)
      contMDiff_const (fun _ => hs)
  let T := G.symm.trans DB
  have hTside (p : RoundCylinderSpace) :
      s < (B.coordinate_inverse (T p)).2 ↔ 0 < p.2 := by
    have h1 := hDBside (G.symm p)
    have h2 := hGside (G.symm p)
    rw [G.apply_symm_apply] at h2
    change (B.coordinate_inverse (DB (G.symm p))).2 ≤ s ↔ (G.symm p).2 ≤ 0 at h1
    have h3 : (B.coordinate_inverse (T p)).2 ≤ s ↔ p.2 ≤ 0 := h1.trans h2.symm
    simpa only [not_le] using not_congr h3
  let U : Set RoundCylinderSpace :=
    {p | |p.2| < rA ∧ |(G.symm p).2| < min R rB}
  have hU : IsOpen U :=
    (isOpen_lt continuous_snd.abs continuous_const).inter
      (isOpen_lt (continuous_snd.comp G.symm.continuous).abs continuous_const)
  have hUzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ U := by
    have hz := hGzero (G.symm (q, 0))
    rw [G.apply_symm_apply] at hz
    have hz' : (G.symm (q, 0)).2 = 0 := hz.mp rfl
    exact ⟨by simpa using hrA, by simpa [hz'] using lt_min hR hrB⟩
  obtain ⟨r, hr, hrcollar⟩ := CylinderGluing.exists_cylinder_collar ⟨U, hU⟩ hUzero
  have hagree (p : RoundCylinderSpace) (hp : |p.2| < r) :
      (DA p : M) = T p := by
    obtain ⟨hpA, hpB⟩ := hrcollar p hp
    let z := G.symm p
    have hmap := hGmap z.1 z.2 (hpB.trans_le (min_le_left _ _))
    have hz : G z = p := G.apply_symm_apply p
    rw [hz] at hmap
    have hDB : (DB z : M) = B.coordinate_map (z.1, s + z.2) := by
      have hzaff := hDBaff z (hpB.trans_le (min_le_right _ _))
      change B.coordinate_inverse (DB z) = (z.1, s + z.2) at hzaff
      have hcoord := B.coordinate_map_coordinate_inverse (DB z).property
      rw [hzaff] at hcoord
      exact hcoord.symm
    have hDA : (DA p : M) = A.coordinate_map (p.1, f p.1 + p.2) := by
      have hpaff := hDAaff p hpA
      change A.coordinate_inverse (DA p) = (p.1, f p.1 + p.2) at hpaff
      have hcoord := A.coordinate_map_coordinate_inverse (DA p).property
      rw [hpaff] at hcoord
      exact hcoord.symm
    exact hDA.trans (hmap.trans hDB.symm)
  refine ⟨r, DA, T, hr, hDAangle, ?_, ?_, hTside, hagree⟩
  · intro q
    simpa using hDAaff (q, 0) (by simpa using hrA)
  · exact hDAside




theorem exists_compatible_neck_cut_charts_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        ∀ s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹,
        (∀ q : UnitTwoSphere, B.coordinate_map (q, s) ∈ A.carrier) →
        ∀ f : UnitTwoSphere → ℝ,
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f →
        (∀ q, f q ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹) →
        range (fun q => A.coordinate_map (q, f q)) =
          range (fun q => B.coordinate_map (q, s)) →
        (∀ x ∈ A.carrier ∩ B.carrier,
          s < (B.coordinate_inverse x).2 ↔
            f (A.coordinate_inverse x).1 < (A.coordinate_inverse x).2) →
        ∃ (r : ℝ)
          (DA : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace B.carrierOpen ∞),
          0 < r ∧
          (∀ p, (A.coordinate_inverse (DA p)).1 = p.1) ∧
          (∀ q, A.coordinate_inverse (DA (q, 0)) = (q, f q)) ∧
          (∀ p, (A.coordinate_inverse (DA p)).2 ≤ f p.1 ↔ p.2 ≤ 0) ∧
          (∀ p, s < (B.coordinate_inverse (T p)).2 ↔ 0 < p.2) ∧
          (∀ p, |p.2| < r → (DA p : M) = T p) := by
  obtain ⟨ε₀, hε₀, hε₀small, hextend⟩ := exists_centered_transition_extension_m28.{u}
  refine ⟨ε₀, hε₀, hε₀small, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB s hs hc f hf hfd hrange hside
  obtain ⟨r, G, hr, hGside, hGzero, hagree⟩ :=
    hextend A B hA hB s hs hc f hf hfd hrange hside
  apply compatible_neck_cut_charts_of_transition A B s hs f hf hfd G r hr hGside hGzero
  intro q t ht
  obtain ⟨_, hct, heq⟩ := hagree t ht
  rw [heq q]
  dsimp only
  have hcancel : f (A.coordinate_inverse (B.coordinate_map (q, s + t))).1 +
      ((A.coordinate_inverse (B.coordinate_map (q, s + t))).2 -
        f (A.coordinate_inverse (B.coordinate_map (q, s + t))).1) =
      (A.coordinate_inverse (B.coordinate_map (q, s + t))).2 := by ring
  rw [hcancel]
  exact A.coordinate_map_coordinate_inverse (hct q)

end PoincareConjecture.EpsilonNeck
