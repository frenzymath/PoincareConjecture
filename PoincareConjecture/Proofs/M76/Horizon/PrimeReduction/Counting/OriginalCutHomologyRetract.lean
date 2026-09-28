import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalSphereCutGraphHomotopyRetract
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits









set_option autoImplicit false
open Set Metric Geometry CategoryTheory AlgebraicTopology

universe u v

namespace PoincareConjecture.M76.CutGraph

variable {K : Type v} [Ring K] (A : ModuleCat.{u} K)
  {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def moduleHomologyMap (f : C(X, Y)) (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of X)).homology A n ⟶
      (TopCat.toSSet.obj (TopCat.of Y)).homology A n :=
  HomologicalComplex.homologyMap
    (((singularChainComplexFunctor (ModuleCat.{u} K)).obj A).map (TopCat.ofHom f)) n

set_option backward.isDefEq.respectTransparency false in


theorem moduleHomologyMap_section_comp (q : C(X, Y)) (s : C(Y, X))
    (H : (q.comp s).Homotopic (ContinuousMap.id Y)) (n : ℕ) :
    moduleHomologyMap A s n ≫ moduleHomologyMap A q n =
      𝟙 ((TopCat.toSSet.obj (TopCat.of Y)).homology A n) := by
  obtain ⟨H⟩ := H
  let HT : TopCat.Homotopy (TopCat.ofHom s ≫ TopCat.ofHom q)
      (𝟙 (TopCat.of Y)) := H
  have hh := HT.congr_homologyMap_singularChainComplexFunctor A n
  unfold moduleHomologyMap
  rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
  calc
    _ = HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{u} K)).obj A).map (𝟙 (TopCat.of Y))) n := hh
    _ = _ := by
      rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
      rfl


theorem moduleHomologyMap_section_injective (q : C(X, Y)) (s : C(Y, X))
    (H : (q.comp s).Homotopic (ContinuousMap.id Y)) (n : ℕ) :
    Function.Injective (moduleHomologyMap A s n) := by
  have hm : Mono (moduleHomologyMap A s n) :=
    mono_of_mono_fac (moduleHomologyMap_section_comp A q s H n)
  exact (ModuleCat.mono_iff_injective _).mp hm

end PoincareConjecture.M76.CutGraph

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_original_cut_homology_retract
    {K : Type v} [Ring K] (A : ModuleCat.{u} K)
    {X κ : Type u} {ι : Type*} [MetricSpace X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (Q : Set X) (hfinite : Finite (ConnectedComponents Q))
      (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)) (O : κ → Set X)
      (D : ConnectedComponents Q → Set X) (ends : κ → Bool → ConnectedComponents Q)
      (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i)),
      letI := hfinite
      letI : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
      letI : DecidableEq (ConnectedComponents Q) := Classical.decEq _
      ∃ (q : C(R, CutGraph.carrier ends)) (s : C(CutGraph.carrier ends, R)),
        Q = R \ ⋃ i, O i ∧ IsCompact Q ∧ PLDomain e Q ∧
        (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧
          IsConnected (closure (O i)) ∧ closure (O i) ⊆ U ∩ interior R) ∧
        Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
        (⋃ i, closure (O i)) ∪ Q = R ∧ Q \ U = R \ U ∧
        (∀ c, IsCompact (D c) ∧ PLDomain e (D c) ∧ IsConnected (D c) ∧ D c ⊆ Q ∧
          frontier (D c) = (D c ∩ frontier R) ∪ ⋃ b ∈ {b | ends b.1 b.2 = c}, B b) ∧
        Pairwise (fun c d => Disjoint (D c) (D d)) ∧ (⋃ c, D c) = Q ∧
        (∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q x) ∧
        (∀ i c, closure (O i) ∩ D c =
          ⋃ b ∈ {b : Bool | ends i b = c}, B (i, b)) ∧
        (∀ i x, (W i (x, 0) : X) = H (i, false) x ∧
          (W i (x, 1) : X) = H (i, true) x) ∧
        (∀ i x, (W i (x, ⟨(1 / 2 : ℝ), by norm_num⟩) : X) = x) ∧
        (∀ v (x : R), (x : X) ∈ D v →
          (q x : CutGraph.Ambient (ConnectedComponents Q) κ) = CutGraph.vertex v) ∧
        (∀ i (x : R) (hi : (x : X) ∈ closure (O i)),
          q x = CutGraph.edgePath ends i (((W i).symm ⟨x, hi⟩).2)) ∧
        (q.comp s).Homotopic (ContinuousMap.id (CutGraph.carrier ends)) ∧
        CutGraph.moduleHomologyMap A s 1 ≫ CutGraph.moduleHomologyMap A q 1 =
          𝟙 ((TopCat.toSSet.obj (TopCat.of (CutGraph.carrier ends))).homology A 1) ∧
        Function.Injective (CutGraph.moduleHomologyMap A s 1) := by
  classical
  obtain ⟨Q, hfinite, B, H, sB, O, D, ends, W, q, s, hQeq, hQ, hQPL, hO, hCC,
    hcover, houtside, hD, hDD, hDcover, hactual, hinc, hW, hcenter, hqD, hqC, hqs⟩ :=
    exists_original_sphere_cut_graph_homotopy_retract S sS hdis hR he hSR hU hSU
  let := hfinite
  let : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
  exact ⟨Q, hfinite, B, H, sB, O, D, ends, W, q, s, hQeq, hQ, hQPL, hO, hCC,
    hcover, houtside, hD, hDD, hDcover, hactual, hinc, hW, hcenter, hqD, hqC, hqs,
    CutGraph.moduleHomologyMap_section_comp A q s hqs 1,
    CutGraph.moduleHomologyMap_section_injective A q s hqs 1⟩

end PoincareConjecture.M76
