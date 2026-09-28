import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ReplacementExteriorCompression
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSmallDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductSlices
import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.PathHomotopy











set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

namespace OriginalDiskProduct
variable {X α : Type*} [TopologicalSpace X]
  {e : α → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

def rimSlice (P : OriginalDiskProduct e R j) (t : I) : C(Q2, frontier R) :=
  ⟨fun x => ⟨P.map ((x : V2),(t : ℝ)),
    (P.proper _ ⟨sphere_subset_closedBall x.property,t.property⟩).mpr x.property⟩,
    (P.polyhedral.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun x => ⟨sphere_subset_closedBall x.property,t.property⟩)).subtype_mk _⟩

def rimSliceHomotopy (P : OriginalDiskProduct e R j) (t : I) :
    (P.rimSlice ⟨0,by norm_num⟩).Homotopy (P.rimSlice t) where
  toFun z := ⟨P.map ((z.2 : V2),(z.1 : ℝ)*(t : ℝ)),
    (P.proper _ ⟨sphere_subset_closedBall z.2.property,by
      constructor
      · nlinarith [z.1.property.1,z.1.property.2,t.property.1,t.property.2]
      · nlinarith [z.1.property.1,z.1.property.2,t.property.1,t.property.2]⟩).mpr z.2.property⟩
  continuous_toFun := (P.polyhedral.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_snd).prodMk
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
    (fun z => ⟨sphere_subset_closedBall z.2.property,by
      change -1 ≤ (z.1 : ℝ)*(t : ℝ) ∧ (z.1 : ℝ)*(t : ℝ) ≤ 1
      constructor
      · nlinarith [z.1.property.1,z.1.property.2,t.property.1,t.property.2]
      · nlinarith [z.1.property.1,z.1.property.2,t.property.1,t.property.2]⟩)).subtype_mk _
  map_zero_left x := by apply Subtype.ext; change P.map ((x : V2),0*(t : ℝ)) = _; rw [zero_mul]; rfl
  map_one_left x := by apply Subtype.ext; change P.map ((x : V2),1*(t : ℝ)) = _; rw [one_mul]; rfl

theorem essential_rimSlice (P : OriginalDiskProduct e R j)
    (hzero : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (Dehn.squareRimLoop.map (P.rimSlice ⟨0,by norm_num⟩).continuous)) ≠ 1)
    (t : I) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (Dehn.squareRimLoop.map (P.rimSlice t).continuous)) ≠ 1 ∧
    ¬ ∃ F : C(D2,frontier R), ∀x:Q2,
      F ⟨x,sphere_subset_closedBall x.property⟩ = P.rimSlice t x := by
  have hnot : ¬ (P.rimSlice t).Nullhomotopic := by
    rintro ⟨y,hy⟩
    have hh : (P.rimSlice ⟨0,by norm_num⟩).Nullhomotopic :=
      ⟨y,(show (P.rimSlice ⟨0,by norm_num⟩).Homotopic (P.rimSlice t) from
        ⟨P.rimSliceHomotopy t⟩).trans hy⟩
    exact hzero (Path.Homotopic.Quotient.eq.mpr
      (Path.Homotopic.map_nullhomotopic_of_nullhomotopic hh Dehn.squareRimLoop))
  have hess : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (Dehn.squareRimLoop.map (P.rimSlice t).continuous)) ≠ 1 := by
    intro hh
    exact hnot (Dehn.nullhomotopic_of_squareRimLoop (P.rimSlice t)
      (Path.Homotopic.Quotient.exact hh))
  refine ⟨hess,?_⟩
  rintro ⟨F,hF⟩
  exact hess (Dehn.squareRimLoop_class_eq_one_of_extension (P.rimSlice t) F hF)

end OriginalDiskProduct

theorem HamiltonMarkedProtectedBall.exists_replacement_exterior_essential_disk_product
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (e' : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
    (he' : PLDomain e' (closure (latticeHandleDomain ι κ L \ D))) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ (j : V2 → LatticeHandleAmbient ι κ L) (P : OriginalDiskProduct e' E j),
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        IsOpen ((Subtype.val : E → LatticeHandleAmbient ι κ L) ⁻¹'
          (P.map '' (D2 ×ˢ Ioo (-ε) ε))) ∧
        IsOpen ((Subtype.val : frontier E → LatticeHandleAmbient ι κ L) ⁻¹'
          (P.map '' (Q2 ×ˢ Ioo (-ε) ε)))) ∧
      ∀ t : I, PolyhedralPLInCharts e' (P.slice t) D2 ∧
        Topology.IsEmbedding (fun x : D2 => P.slice t x) ∧
        MapsTo (P.slice t) D2 E ∧
        (∀ x : D2, P.slice t x ∈ frontier E ↔ x.val ∈ Q2) ∧
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (Dehn.squareRimLoop.map (P.rimSlice t).continuous)) ≠ 1 ∧
        ¬ ∃ F : C(D2,frontier E), ∀x:Q2,
          F ⟨x,sphere_subset_closedBall x.property⟩ = P.rimSlice t x := by
  dsimp only
  let E := closure (latticeHandleDomain ι κ L \ D)
  obtain ⟨j,rim,hj,hji,hjE,hrim,hproper,hessential,_⟩ :=
    b.exists_replacement_exterior_essential_disk he hdim hi e' he'
  have hE : IsCompact E := (b.closed_complement_geometry he hdim hi).1
  obtain ⟨P,_,hopen⟩ := exists_small_original_disk_product hE he' hj hji hjE hproper
    isOpen_univ (subset_univ _)
  have hzero : P.rimSlice ⟨0,by norm_num⟩ = rim := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact (P.central x (sphere_subset_closedBall x.property)).trans (hrim x)
  have hesszero : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (Dehn.squareRimLoop.map (P.rimSlice ⟨0,by norm_num⟩).continuous)) ≠ 1 := by
    rw [hzero]
    exact hessential
  refine ⟨j,P,hopen,?_⟩
  intro t
  exact ⟨P.polyhedral_slice t.property,P.embedding_slice t.property,
    P.slice_inside t.property,P.slice_proper t.property,(P.essential_rimSlice hesszero t).1,
    (P.essential_rimSlice hesszero t).2⟩

end PoincareConjecture.M76

