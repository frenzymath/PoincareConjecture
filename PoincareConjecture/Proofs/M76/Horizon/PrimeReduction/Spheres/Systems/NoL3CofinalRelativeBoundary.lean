import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3NestedRelativeBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalRawSphereCut









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.exists_finer_original_cut_relative_boundary
    {X E ι κ : Type*} [MetricSpace X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R Q₀ U : Set X} (O₀ S : κ → Set X)
    (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure (O₀ i.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ i, B₀ i)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    ∃ (Q : Set X) (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)) (O : κ → Set X)
      (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i)),
      Q₀ ⊆ Q ∧ HasNoPuncturedSphereComponents e f Q ∧
      Q = R \ ⋃ i, O i ∧ IsCompact Q ∧ PLDomain e Q ∧
      (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧
        IsConnected (closure (O i)) ∧ closure (O i) ⊆ U ∩ interior R) ∧
      Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
      (∀ i, closure (O i) ∩ Q = B (i,false) ∪ B (i,true)) ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      (∀ b, B b ⊆ closure (O b.1)) ∧
      frontier Q = frontier R ∪ ⋃ b, B b ∧
      (∀ i x, (W i (x,0) : X) = H (i,false) x ∧
        (W i (x,1) : X) = H (i,true) x) ∧
      (∀ i x, (W i (x,⟨(1/2 : ℝ),by norm_num⟩) : X) = x) ∧
      (∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ i, S i ⊆ closure (O i)) ∧
      (∀ x ∈ Q, connectedComponentIn Q x = connectedComponentIn (R \ ⋃ i, S i) x ∩ Q) ∧
      ∀ x ∈ R \ ⋃ i, S i, (connectedComponentIn (R \ ⋃ i, S i) x ∩ Q).Nonempty := by
  have hSO₀ (i : κ) : S i ⊆ O₀ i := by
    intro x hx
    let z := (W₀ i).symm ⟨x,hSC₀ i hx⟩
    have hz : (W₀ i z : X) = x := congrArg Subtype.val ((W₀ i).apply_symm_apply _)
    have ht := (hcenter₀ i z).mp (hz.symm ▸ hx)
    exact hz ▸ (hopen₀ i z).mpr (by rw [ht]; norm_num)
  let V := U ∩ ⋃ i, O₀ i
  have hV : IsOpen V := hU.inter (isOpen_iUnion hO₀)
  have hSV (i : κ) : S i ⊆ V := fun x hx => ⟨hSU i hx,mem_iUnion.mpr ⟨i,hSO₀ i hx⟩⟩
  obtain ⟨Q,B,H,sB,O,W,r,hQeq,hQ,hQPL,hO,hCC,hinc,hBB,hfront,hW,hcenter,
      hopen,hS,hSC,_,hrQ,_,hrcc,hcomp,_⟩ :=
    exists_original_cut_with_raw_components S sS hdis hR he hSR hV hSV
  have hnest : Q₀ ⊆ Q := by
    intro x hx
    have hx' := hQ₀eq.subset hx
    apply hQeq.symm.subset
    refine ⟨hx'.1,?_⟩
    intro hxO
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxO
    exact hx'.2 ((hO i).2.2.2 (subset_closure hi)).1.2
  have hBsub (b : κ × Bool) : B b ⊆ closure (O b.1) := by
    intro x hx
    have hh : x ∈ B (b.1,false) ∪ B (b.1,true) := by
      rcases b with ⟨i,b⟩
      cases b
      · exact Or.inl hx
      · exact Or.inr hx
    exact ((hinc b.1).symm.subset hh).1
  let Qs : Bool → Set X := fun b => if b then Q else Q₀
  let Os : Bool → κ → Set X := fun b => if b then O else O₀
  let Bs : Bool → κ × Bool → Set X := fun b => if b then B else B₀
  let Ws : ∀ b i, (S i × unitInterval) ≃ₜ closure (Os b i) := fun b => by
    cases b
    · exact W₀
    · exact W
  have hnew : HasNoPuncturedSphereComponents e f Q := by
    apply HasNoPuncturedSphereComponents.mono_original_collar_cut_relative_boundary
      R hR.isClosed Qs Os S Ws
      (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
      (by
        intro b i
        cases b
        · exact hCR₀ i
        · exact (hO i).2.2.2.trans inter_subset_right)
      (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
      Bs (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption)
      (by intro b; cases b <;> assumption) hnest L g hg hgi hreal hno
  refine ⟨Q,B,H,sB,O,W,hnest,hnew,hQeq,hQ,hQPL,?_,hCC,hinc,hBB,hBsub,hfront,
    hW,hcenter,hopen,hS,hSC,hcomp,?_⟩
  · intro i
    exact ⟨(hO i).1,(hO i).2.1,(hO i).2.2.1,
      fun x hx => ⟨((hO i).2.2.2 hx).1.1,((hO i).2.2.2 hx).2⟩⟩
  · intro x hx
    exact ⟨r x,hrcc x hx,hrQ hx⟩

end PoincareConjecture.M76
