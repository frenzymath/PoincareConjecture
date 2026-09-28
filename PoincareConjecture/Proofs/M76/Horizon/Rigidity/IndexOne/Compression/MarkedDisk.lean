import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.MarkedLoopImage

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

private theorem exists_squareRim_filling_essential_image
    {Y Z W : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
    (i : C(Y, Z)) (u : C(Y, W)) (y : Y) (c : FundamentalGroup Y y)
    (hc : FundamentalGroup.map i y c = 1) (hu : FundamentalGroup.map u y c ≠ 1) :
    ∃ (gamma : C(Q, Y)) (f : C(D, Z)),
      (∀ z : Q, f ⟨z, sphere_subset_closedBall z.property⟩ = i (gamma z)) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((Dehn.squareRimLoop.map gamma.continuous).map u.continuous)) ≠ 1 := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective c
  obtain ⟨gamma, hgamma⟩ := Dehn.exists_squareRimMap p
  have hbase : gamma Dehn.squareRimBase = y := by
    simpa only [Path.source] using hgamma 0
  have hpi : (p.map i.continuous).Homotopic (Path.refl (i y)) :=
    Path.Homotopic.Quotient.exact hc
  have hloop : (Dehn.squareRimLoop.map (i.comp gamma).continuous) =
      (p.map i.continuous).cast (congrArg i hbase) (congrArg i hbase) := by
    ext t
    exact congrArg i (hgamma t)
  have hnull : (i.comp gamma).Nullhomotopic := by
    apply Dehn.nullhomotopic_of_squareRimLoop
    rw [hloop]
    have href : (Path.refl (i y)).cast (congrArg i hbase) (congrArg i hbase) =
        Path.refl ((i.comp gamma) Dehn.squareRimBase) := by
      ext t
      exact (congrArg i hbase).symm
    simpa only [href] using hpi.pathCast (congrArg i hbase) (congrArg i hbase)
  obtain ⟨f, hf⟩ := hnull.exists_closedBall_extension (i.comp gamma)
  refine ⟨gamma, f, hf, ?_⟩
  intro htrivial
  have hgp : ((Dehn.squareRimLoop.map gamma.continuous).map u.continuous).Homotopic
      (Path.refl (u (gamma Dehn.squareRimBase))) := Path.Homotopic.Quotient.exact htrivial
  have heq : ((Dehn.squareRimLoop.map gamma.continuous).map u.continuous).cast
      (congrArg u hbase.symm) (congrArg u hbase.symm) = p.map u.continuous := by
    ext t
    exact congrArg u (hgamma t)
  have href : (Path.refl (u (gamma Dehn.squareRimBase))).cast
      (congrArg u hbase.symm) (congrArg u hbase.symm) = Path.refl (u y) := by
    ext t
    exact congrArg u hbase
  apply hu
  apply Path.Homotopic.Quotient.eq.mpr
  simpa only [heq, href] using
    hgp.pathCast (congrArg u hbase.symm) (congrArg u hbase.symm)

theorem kernel_le_or_exists_marked_disk
    {X α Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (e : α → OpenPartialHomeomorph X V3) {N M : Set X}
    (hN : PLDomain e N) (hMN : M ⊆ N) (hMfront : M ⊆ frontier N)
    (hMopen : IsOpen ((Subtype.val : frontier N → X) ⁻¹' M))
    (u : C(M, Y)) (x : M) :
    (∀ c : FundamentalGroup M x,
      FundamentalGroup.map (ContinuousMap.inclusion hMN) x c = 1 →
        FundamentalGroup.map u x c = 1) ∨
      ∃ (j : V2 → X) (rim : C(Q, M)),
        PolyhedralPLInCharts e j D ∧
        Topology.IsEmbedding (fun z : D => j z) ∧ MapsTo j D N ∧
        (∀ z : Q, j z = (rim z : X)) ∧
        (∀ z : D, j z ∈ frontier N ↔ (z : V2) ∈ Q) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((Dehn.squareRimLoop.map rim.continuous).map u.continuous)) ≠ 1 := by
  classical
  by_cases h : ∀ c : FundamentalGroup M x,
      FundamentalGroup.map (ContinuousMap.inclusion hMN) x c = 1 →
        FundamentalGroup.map u x c = 1
  · exact Or.inl h
  push Not at h
  obtain ⟨c, hc, hu⟩ := h
  obtain ⟨gamma, f, hf, he⟩ := exists_squareRim_filling_essential_image
    (ContinuousMap.inclusion hMN) u x c hc hu
  exact Or.inr (Dehn.exists_marked_boundary_disk_with_essential_image
    e N hN M hMfront hMopen f gamma (fun z => congrArg Subtype.val (hf z)) u he)

end PoincareConjecture.M76.HamiltonIntervalTorus
