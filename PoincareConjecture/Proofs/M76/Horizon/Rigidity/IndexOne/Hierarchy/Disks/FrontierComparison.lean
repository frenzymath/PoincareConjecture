import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.FillingReflection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.MarkedLoopImage
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.EssentialSquareRim

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_square_filling_of_homotopic_boundary
    {X : Type*} [TopologicalSpace X] (gamma : C(Q, X)) (disk : C(D, X))
    (hom : gamma.Homotopic
      (disk.comp ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩, by fun_prop⟩)) :
    ∃ filling : C(D, X),
      ∀ x : Q, filling ⟨x, sphere_subset_closedBall x.property⟩ = gamma x := by
  let : ContractibleSpace D := (convex_closedBall (0 : V2) 1).contractibleSpace
    ⟨0, mem_closedBall_self (by norm_num)⟩
  let inc : C(Q, D) := ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩, by fun_prop⟩
  have hdisk : disk.Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic D).comp_right disk
  obtain ⟨x, hx⟩ := hdisk.comp_left inc
  exact (show gamma.Nullhomotopic from ⟨x, hom.trans hx⟩).exists_closedBall_extension gamma

theorem exists_proper_marked_disk_of_frontier_comparison
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    (e : α → OpenPartialHomeomorph X V3) {N T : Set X}
    (hN : PLDomain e N)
    (hinj : ∀ x : N, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, X)) x))
    (E : ↥(frontier N) ≃ₜ ↥(frontier T))
    (hom : (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier N, X)).Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(frontier T, X)).comp ⟨E, E.continuous⟩))
    (F : Set X) (hF : F ⊆ frontier N)
    (hFopen : IsOpen ((Subtype.val : frontier N → X) ⁻¹' F))
    (gamma : C(Q, F)) (targetDisk : C(D, T))
    (hboundary : ∀ x : Q,
      (targetDisk ⟨x, sphere_subset_closedBall x.property⟩ : X) =
        (E (Set.inclusion hF (gamma x)) : X))
    (retract : C(frontier T, Q))
    (hleft : ∀ x, retract (E (Set.inclusion hF (gamma x))) = x) :
    ∃ (j : V2 → X) (rim : C(Q, F)),
      PolyhedralPLInCharts e j D ∧ Topology.IsEmbedding (fun x : D => j x) ∧ MapsTo j D N ∧
      (∀ x : Q, j x = (rim x : X)) ∧
      (∀ x : D, j x ∈ frontier N ↔ (x : V2) ∈ Q) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((Dehn.squareRimLoop.map rim.continuous).map
          ((retract.comp ⟨E, E.continuous⟩).comp (ContinuousMap.inclusion hF)).continuous)) ≠ 1 := by
  let gammaFront := (ContinuousMap.inclusion hF).comp gamma
  let iN : C(N, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let gammaN : C(Q, N) := (ContinuousMap.inclusion hN.closed.frontier_subset).comp gammaFront
  let diskX : C(D, X) := (⟨Subtype.val, continuous_subtype_val⟩ : C(T, X)).comp targetDisk
  let inc : C(Q, D) := ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩, by fun_prop⟩
  have hhom : (iN.comp gammaN).Homotopic (diskX.comp inc) := by
    have hh := hom.comp (ContinuousMap.Homotopic.refl gammaFront)
    have heq : ((⟨Subtype.val, continuous_subtype_val⟩ : C(frontier T, X)).comp
        ⟨E, E.continuous⟩).comp gammaFront = diskX.comp inc := by
      apply ContinuousMap.ext
      intro x
      change (E (Set.inclusion hF (gamma x)) : X) =
        (targetDisk ⟨x, sphere_subset_closedBall x.property⟩ : X)
      exact (hboundary x).symm
    exact heq ▸ hh
  obtain ⟨ambient, hambient⟩ := exists_square_filling_of_homotopic_boundary
    (iN.comp gammaN) diskX hhom
  obtain ⟨f, hf⟩ := Dehn.exists_square_filling_in_subset gammaN
    (hinj (gammaN Dehn.squareRimBase)) ambient hambient
  let u := (retract.comp ⟨E, E.continuous⟩).comp (ContinuousMap.inclusion hF)
  have hess : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((Dehn.squareRimLoop.map gamma.continuous).map u.continuous)) ≠ 1 := by
    have hmap : u.comp gamma = ContinuousMap.id Q := by
      apply ContinuousMap.ext
      intro x
      exact hleft x
    have hleft' : ∀ x, u (gamma x) = x := fun x => congrArg (fun f : C(Q, Q) => f x) hmap
    intro hn
    have hunit : FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk Dehn.squareRimLoop) = 1 := by
      have hn' := Path.Homotopic.Quotient.eq.mp hn
      have hh := hn'.pathCast (hleft' Dehn.squareRimBase).symm
        (hleft' Dehn.squareRimBase).symm
      apply Path.Homotopic.Quotient.eq.mpr
      convert hh using 1 <;> apply Path.ext <;> funext t
      · exact (hleft' (Dehn.squareRimLoop t)).symm
      · exact (hleft' Dehn.squareRimBase).symm
    exact Dehn.squareRimLoop_class_ne_one hunit
  exact Dehn.exists_marked_boundary_disk_with_essential_image e N hN F
    hF hFopen f gamma (fun x => congrArg Subtype.val (hf x)) u hess

theorem exists_proper_disk_of_frontier_comparison
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    (e : α → OpenPartialHomeomorph X V3) {N T : Set X}
    (hN : PLDomain e N)
    (hinj : ∀ x : N, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, X)) x))
    (E : ↥(frontier N) ≃ₜ ↥(frontier T))
    (hom : (⟨Subtype.val, continuous_subtype_val⟩ : C(frontier N, X)).Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(frontier T, X)).comp ⟨E, E.continuous⟩))
    (targetDisk : C(D, T)) (targetRim : C(Q, frontier T))
    (hboundary : ∀ x : Q,
      (targetDisk ⟨x, sphere_subset_closedBall x.property⟩ : X) = (targetRim x : X))
    (retract : C(frontier T, Q)) (hleft : ∀ x, retract (targetRim x) = x) :
    ∃ (j : V2 → X) (rim : C(Q, frontier N)),
      PolyhedralPLInCharts e j D ∧ Topology.IsEmbedding (fun x : D => j x) ∧ MapsTo j D N ∧
      (∀ x : Q, j x = (rim x : X)) ∧
      (∀ x : D, j x ∈ frontier N ↔ (x : V2) ∈ Q) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((Dehn.squareRimLoop.map rim.continuous).map
          (retract.comp ⟨E, E.continuous⟩).continuous)) ≠ 1 := by
  let gamma := (⟨E.symm, E.symm.continuous⟩ : C(frontier T, frontier N)).comp targetRim
  have hopen : IsOpen ((Subtype.val : frontier N → X) ⁻¹' frontier N) := by
    have heq : (Subtype.val : frontier N → X) ⁻¹' frontier N = univ := by
      ext x
      simp only [mem_preimage, x.property, mem_univ]
    rw [heq]
    exact isOpen_univ
  exact exists_proper_marked_disk_of_frontier_comparison e hN hinj E hom
    (frontier N) subset_rfl hopen gamma targetDisk
    (fun x => by simpa only [gamma, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      Set.inclusion_mk, E.apply_symm_apply] using hboundary x)
    retract (fun x => by simpa only [gamma, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      Set.inclusion_mk, E.apply_symm_apply] using hleft x)

end PoincareConjecture.M76.HamiltonIntervalTorus
