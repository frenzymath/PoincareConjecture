import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.SlabParameter
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Gluing.PhasePartition
import PoincareConjecture.Proofs.M76.Mathlib.CompactHomeomorphGluing

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
  (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space

variable {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
  {d : β → OpenPartialHomeomorph X V3} {phi : C(H, H)}
  {M : PairedMeridianHierarchy e d phi} {uv : ℝ × ℝ}

structure StandardToSourceSlab (m : ExactSlabMeridian M uv) where
  map : sourceSlab (ContinuousMap.id H) uv.1 uv.2 ≃ₜ sourceSlab M.eta uv.1 uv.2
  parameter : V2 × ℝ → X
  parameter_pl : PolyhedralPLInCharts e parameter (D ×ˢ Icc (0 : ℝ) p)
  period_eq : ∀ z : D, ∀ t ∈ Icc (0 : ℝ) p,
    (map (standardSlabMeridianCoordinates uv.1 uv.2 m.ordered m.short (z, (t : C))) : X) =
      parameter (z, t)
  frontier_eq : ∀ (x : sourceSlab (ContinuousMap.id H) uv.1 uv.2)
    (hx : (x : X) ∈ frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2)),
    (map x : X) = m.frontierMap.symm ⟨x, hx⟩

theorem ExactSlabMeridian.exists_standardToSourceSlab (m : ExactSlabMeridian M uv)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ))) :
    Nonempty (StandardToSourceSlab m) := by
  obtain ⟨G, f, hf, hperiod, hfront⟩ := m.exists_slab_parameter hd huv
  let T := standardSlabMeridianCoordinates uv.1 uv.2 m.ordered m.short
  refine ⟨⟨T.symm.trans G, f, hf, ?_, ?_⟩⟩
  · intro z t ht
    simpa only [T, Homeomorph.trans_apply, Homeomorph.symm_apply_apply] using hperiod z t ht
  · intro x hx
    let y := (standardSlabBoundaryCoordinates uv.1 uv.2 m.ordered m.short).symm ⟨x, hx⟩
    have hxy : T (⟨y.1, sphere_subset_closedBall y.1.property⟩, y.2) = x := by
      apply Subtype.ext
      change (standardSlabBoundaryCoordinates uv.1 uv.2 m.ordered m.short y : X) = x
      exact congrArg (fun z : frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2) => (z : X))
        ((standardSlabBoundaryCoordinates uv.1 uv.2 m.ordered m.short).apply_symm_apply ⟨x, hx⟩)
    calc
      ((T.symm.trans G) x : X) = G (⟨y.1, sphere_subset_closedBall y.1.property⟩, y.2) := by
        rw [← hxy, Homeomorph.trans_apply, T.symm_apply_apply]
      _ = m.frontierCylinderCoordinates y := hfront y.1 y.2
      _ = _ := ?_
    change (m.frontierMap.symm
      (standardSlabBoundaryCoordinates uv.1 uv.2 m.ordered m.short y) : X) = _
    rw [Homeomorph.apply_symm_apply]

namespace StandardToSourceSlab

variable {m : ExactSlabMeridian M uv} (S : StandardToSourceSlab m)

private theorem target_frontier (m : ExactSlabMeridian M uv) :
    frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2) =
      (sourceSlab (ContinuousMap.id H) uv.1 uv.2 ∩ frontier R) ∪
        (sourceSurface (ContinuousMap.id H) (uv.1 : C) ∪
          sourceSurface (ContinuousMap.id H) (uv.2 : C)) := by
  exact frontier_standard_sourceSlab
    (a := uv.1) (b := uv.2) (c := (uv.1 + uv.2 - p) / 2)
    (by linarith [m.short]) m.ordered.le (by linarith [m.short])

private theorem phases_eq
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ))) :
    ({(uv.1 : C), (uv.2 : C)} : Set C) = {(M.a : C), (M.b : C)} := by
  rcases huv with rfl | rfl
  · rfl
  · simp only [AddCircle.coe_add_period]
    exact pair_comm _ _

theorem map_phase
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ)))
    (theta : C) (htheta : theta ∈ ({(M.a : C), (M.b : C)} : Set C))
    (x : sourceSlab (ContinuousMap.id H) uv.1 uv.2)
    (hx : (x : X) ∈ sourceSurface (ContinuousMap.id H) theta) :
    (S.map x : X) = M.annuli theta htheta ((standardTargetAnnulus theta).symm ⟨x, hx⟩) := by
  have ht : theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C) := (phases_eq huv).symm ▸ htheta
  have hxf : (x : X) ∈ frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2) := by
    apply (target_frontier (m := m)).symm.subset
    right
    rcases ht with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx
  let z := M.annuli theta htheta ((standardTargetAnnulus theta).symm ⟨x, hx⟩)
  have hzf : (z : X) ∈ frontier (sourceSlab M.eta uv.1 uv.2) := by
    apply (M.geometry.frontiers uv huv).symm.subset
    right
    rcases ht with rfl | rfl
    · exact Or.inl z.property
    · exact Or.inr z.property
  have hzmap : m.frontierMap ⟨z, hzf⟩ = ⟨x, hxf⟩ := by
    apply Subtype.ext
    rw [m.annulus_marks theta htheta z hzf]
    simp only [z, Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
  rw [S.frontier_eq x hxf, ← hzmap, Homeomorph.symm_apply_apply]

theorem map_mem_phase_iff
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ)))
    (theta : C) (htheta : theta ∈ ({(M.a : C), (M.b : C)} : Set C))
    (x : sourceSlab (ContinuousMap.id H) uv.1 uv.2) :
    (S.map x : X) ∈ sourceSurface M.eta theta ↔
      (x : X) ∈ sourceSurface (ContinuousMap.id H) theta := by
  constructor
  · intro hx
    let z := standardTargetAnnulus theta ((M.annuli theta htheta).symm ⟨S.map x, hx⟩)
    have ht : theta ∈ ({(uv.1 : C), (uv.2 : C)} : Set C) := (phases_eq huv).symm ▸ htheta
    have hzf : (z : X) ∈ frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2) := by
      apply (target_frontier (m := m)).symm.subset
      right
      rcases ht with rfl | rfl
      · exact Or.inl z.property
      · exact Or.inr z.property
    have hzN := (sourceSlab_isCompact (ContinuousMap.id H) uv.1 uv.2).isClosed.frontier_subset hzf
    have heq : S.map ⟨z, hzN⟩ = S.map x := by
      apply Subtype.ext
      rw [S.map_phase huv theta htheta _ z.property]
      change (M.annuli theta htheta ((standardTargetAnnulus theta).symm
        (standardTargetAnnulus theta ((M.annuli theta htheta).symm ⟨S.map x, hx⟩))) : X) = _
      rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
    have hzx : (z : X) = x := congrArg Subtype.val (S.map.injective heq)
    exact hzx ▸ z.property
  · intro hx
    rw [S.map_phase huv theta htheta x hx]
    exact (M.annuli theta htheta _).property

theorem map_fixed_old
    (huv : uv ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ)))
    (x : sourceSlab (ContinuousMap.id H) uv.1 uv.2) (hx : (x : X) ∈ frontier R) :
    (S.map x : X) = x := by
  have hxf : (x : X) ∈ frontier (sourceSlab (ContinuousMap.id H) uv.1 uv.2) :=
    (target_frontier (m := m)).symm.subset (Or.inl ⟨x.property, hx⟩)
  have hxold : (x : X) ∈ sourceSlab M.eta uv.1 uv.2 ∩ frontier R :=
    (old_sourceSlab_eq_of_relative_maps M.eta (ContinuousMap.id H) uv.1 uv.2
      M.identity_homotopy (.refl _ _)).symm.subset ⟨x.property, hx⟩
  have hxs : (x : X) ∈ frontier (sourceSlab M.eta uv.1 uv.2) :=
    (M.geometry.frontiers uv huv).symm.subset (Or.inl hxold)
  have heq : m.frontierMap ⟨x, hxs⟩ = ⟨x, hxf⟩ := Subtype.ext (m.fixed_old _ hx)
  rw [S.frontier_eq x hxf, ← heq, Homeomorph.symm_apply_apply]

end StandardToSourceSlab

theorem exists_paired_slab_homeomorph
    {m₀ : ExactSlabMeridian M (M.a, M.b)}
    {m₁ : ExactSlabMeridian M (M.b, M.a + p)}
    (S₀ : StandardToSourceSlab m₀) (S₁ : StandardToSourceSlab m₁) :
    ∃ E : R ≃ₜ R,
      (∀ x : sourceSlab (ContinuousMap.id H) M.a M.b,
        (E ⟨x, sourceSlab_subset _ _ _ x.property⟩ : X) = S₀.map x) ∧
      (∀ x : sourceSlab (ContinuousMap.id H) M.b (M.a + p),
        (E ⟨x, sourceSlab_subset _ _ _ x.property⟩ : X) = S₁.map x) ∧
      ∀ x : R, (x : X) ∈ frontier R → E x = x := by
  have ha : 0 < M.a := by linarith [M.a_range.1]
  have hab : M.a < M.b := by linarith [M.a_range.2, M.b_range.1]
  have hb : M.b < p := by linarith [M.b_range.2]
  have h₀ : (M.a, M.b) ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ)) := by simp
  have h₁ : (M.b, M.a + p) ∈ ({(M.a, M.b), (M.b, M.a + p)} : Set (ℝ × ℝ)) := by simp
  have htarget := sourceSlab_complementary_partition (ContinuousMap.id H) ha hab hb
  have hsource := sourceSlab_complementary_partition M.eta ha hab hb
  have hoverlap (x : sourceSlab (ContinuousMap.id H) M.a M.b) :
      (x : X) ∈ sourceSlab (ContinuousMap.id H) M.b (M.a + p) ↔
        (S₀.map x : X) ∈ sourceSlab M.eta M.b (M.a + p) := by
    have ht : (x : X) ∈ sourceSlab (ContinuousMap.id H) M.b (M.a + p) ↔
        (x : X) ∈ sourceSurface (ContinuousMap.id H) (M.a : C) ∪
          sourceSurface (ContinuousMap.id H) (M.b : C) := by
      rw [← htarget.2]
      exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
    have hs : (S₀.map x : X) ∈ sourceSlab M.eta M.b (M.a + p) ↔
        (S₀.map x : X) ∈ sourceSurface M.eta (M.a : C) ∪
          sourceSurface M.eta (M.b : C) := by
      rw [← hsource.2]
      exact ⟨fun hx => ⟨(S₀.map x).property, hx⟩, fun hx => hx.2⟩
    rw [ht, hs, mem_union, mem_union,
      S₀.map_mem_phase_iff h₀ (M.a : C) (by simp),
      S₀.map_mem_phase_iff h₀ (M.b : C) (by simp)]
  have hagree (x : X) (hx₀ : x ∈ sourceSlab (ContinuousMap.id H) M.a M.b)
      (hx₁ : x ∈ sourceSlab (ContinuousMap.id H) M.b (M.a + p)) :
      (S₀.map ⟨x, hx₀⟩ : X) = S₁.map ⟨x, hx₁⟩ := by
    have hx := htarget.2.subset ⟨hx₀, hx₁⟩
    rcases hx with hx | hx
    · rw [S₀.map_phase h₀ (M.a : C) (by simp) _ hx,
        S₁.map_phase h₁ (M.a : C) (by simp) _ hx]
    · rw [S₀.map_phase h₀ (M.b : C) (by simp) _ hx,
        S₁.map_phase h₁ (M.b : C) (by simp) _ hx]
  obtain ⟨E₀, hE₀, hE₁⟩ := Homeomorph.exists_union_of_compact
    (sourceSlab_isCompact (ContinuousMap.id H) M.a M.b)
    (sourceSlab_isCompact (ContinuousMap.id H) M.b (M.a + p))
    S₀.map S₁.map hoverlap hagree
  let E : R ≃ₜ R := (Homeomorph.setCongr htarget.1.symm).trans
    (E₀.trans (Homeomorph.setCongr hsource.1))
  have hleft (x : sourceSlab (ContinuousMap.id H) M.a M.b) :
      (E ⟨x, sourceSlab_subset _ _ _ x.property⟩ : X) = S₀.map x := hE₀ x
  have hright (x : sourceSlab (ContinuousMap.id H) M.b (M.a + p)) :
      (E ⟨x, sourceSlab_subset _ _ _ x.property⟩ : X) = S₁.map x := hE₁ x
  refine ⟨E, hleft, hright, ?_⟩
  intro x hx
  apply Subtype.ext
  rcases htarget.1.symm.subset x.property with hx₀ | hx₁
  · exact (hleft ⟨x, hx₀⟩).trans (S₀.map_fixed_old h₀ ⟨x, hx₀⟩ hx)
  · exact (hright ⟨x, hx₁⟩).trans (S₁.map_fixed_old h₁ ⟨x, hx₁⟩ hx)

theorem exists_original_paired_slab_homeomorph
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (m₀ : ExactSlabMeridian M (M.a, M.b))
    (m₁ : ExactSlabMeridian M (M.b, M.a + p)) :
    ∃ (S₀ : StandardToSourceSlab m₀) (S₁ : StandardToSourceSlab m₁) (E : R ≃ₜ R),
      (∀ x : sourceSlab (ContinuousMap.id H) M.a M.b,
        (E ⟨x, sourceSlab_subset _ _ _ x.property⟩ : X) = S₀.map x) ∧
      (∀ x : sourceSlab (ContinuousMap.id H) M.b (M.a + p),
        (E ⟨x, sourceSlab_subset _ _ _ x.property⟩ : X) = S₁.map x) ∧
      ∀ x : R, (x : X) ∈ frontier R → E x = x := by
  obtain ⟨S₀⟩ := m₀.exists_standardToSourceSlab hd (by simp)
  obtain ⟨S₁⟩ := m₁.exists_standardToSourceSlab hd (by simp)
  obtain ⟨E, hE₀, hE₁, hfix⟩ := exists_paired_slab_homeomorph S₀ S₁
  exact ⟨S₀, S₁, E, hE₀, hE₁, hfix⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
