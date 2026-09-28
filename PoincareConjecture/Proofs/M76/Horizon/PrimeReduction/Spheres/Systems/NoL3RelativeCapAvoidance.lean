import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3CofinalRelativeBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SelectedOriginalCutDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperDiskSelectedHole









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.exists_relative_cut_avoiding_cap
    {X E ι κ : Type*} [MetricSpace X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R Q₀ D : Set X} (O₀ S : κ → Set X)
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
    (hR : IsCompact R) (he : PLDomain e R) (hSR : ∀ i, S i ⊆ interior R)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (i : κ) (hD : IsCompact D) (hDother : ∀ j, j ≠ i → Disjoint D (S j)) :
    ∃ (Q : Set X) (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)) (O : κ → Set X)
      (W : ∀ j, (S j × unitInterval) ≃ₜ closure (O j)),
      Q₀ ⊆ Q ∧ HasNoPuncturedSphereComponents e f Q ∧
      Q = R \ ⋃ j, O j ∧ IsCompact Q ∧ PLDomain e Q ∧
      (∀ j, IsOpen (O j) ∧ IsCompact (closure (O j)) ∧
        IsConnected (closure (O j)) ∧ closure (O j) ⊆ interior R) ∧
      Pairwise (fun j k => Disjoint (closure (O j)) (closure (O k))) ∧
      (∀ j, closure (O j) ∩ Q = B (j,false) ∪ B (j,true)) ∧
      Pairwise (fun b d => Disjoint (B b) (B d)) ∧
      (∀ b, B b ⊆ closure (O b.1)) ∧
      frontier Q = frontier R ∪ ⋃ b, B b ∧
      (∀ j x, (W j (x,0) : X) = H (j,false) x ∧
        (W j (x,1) : X) = H (j,true) x) ∧
      (∀ j x, (W j (x,⟨(1/2 : ℝ),by norm_num⟩) : X) = x) ∧
      (∀ j z, (W j z : X) ∈ O j ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ j z, (W j z : X) ∈ S j ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ j, S j ⊆ closure (O j)) ∧
      (∀ j, closure (O j) ⊆ closure (O₀ j)) ∧
      ∀ j, j ≠ i → Disjoint D (closure (O j)) := by
  classical
  have hSO₀ (j : κ) : S j ⊆ O₀ j := by
    intro x hx
    let z := (W₀ j).symm ⟨x,hSC₀ j hx⟩
    have hz : (W₀ j z : X) = x := congrArg Subtype.val ((W₀ j).apply_symm_apply _)
    have ht := (hcenter₀ j z).mp (hz.symm ▸ hx)
    exact hz ▸ (hopen₀ j z).mpr (by rw [ht]; norm_num)
  let U := (O₀ i ∪ Dᶜ) ∩ ⋃ j, O₀ j
  have hU : IsOpen U := ((hO₀ i).union hD.isClosed.isOpen_compl).inter (isOpen_iUnion hO₀)
  have hSU (j : κ) : S j ⊆ U := by
    intro x hx
    refine ⟨?_,mem_iUnion.mpr ⟨j,hSO₀ j hx⟩⟩
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hSO₀ j hx)
    · exact Or.inr (fun h => disjoint_left.mp (hDother j hji) h hx)
  obtain ⟨Q,B,H,sB,O,W,hQQ,hnoQ,hQeq,hQ,hQPL,hO,hOdis,hinc,hBdis,hBsub,hfront,
      hW,hcenter,hopen,hS,hSC,_,_⟩ :=
    hno.exists_finer_original_cut_relative_boundary O₀ S W₀ hQ₀eq hQ₀ hQ₀PL hO₀ hCR₀ hdis₀
      hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ sS hdis hR he hSR hU hSU
      L g hg hgi hreal
  have hnest (j : κ) : closure (O j) ⊆ closure (O₀ j) := by
    have hcover : closure (O j) ⊆ ⋃ k, closure (O₀ k) := by
      intro x hx
      obtain ⟨k,hk⟩ := mem_iUnion.mp ((hO j).2.2.2 hx).1.2
      exact mem_iUnion.mpr ⟨k,subset_closure hk⟩
    obtain ⟨k,hk,_⟩ := (hO j).2.2.1.exists_unique_subset_finite_disjoint_closed
      (fun k => closure (O₀ k)) (fun _ => isClosed_closure) hdis₀ hcover
    obtain ⟨z,hz⟩ := (show (Metric.sphere (0 : V3) 1).Nonempty from
      NormedSpace.sphere_nonempty.mpr zero_le_one)
    let x : S j := (sS j).parametrization ⟨z,hz⟩
    have hkj : k = j := by
      by_contra hne
      exact disjoint_left.mp (hdis₀ hne) (hk (hSC j x.property)) (hSC₀ j x.property)
    exact hkj ▸ hk
  refine ⟨Q,B,H,sB,O,W,hQQ,hnoQ,hQeq,hQ,hQPL,
    fun j => ⟨(hO j).1,(hO j).2.1,(hO j).2.2.1,
      (hO j).2.2.2.trans inter_subset_right⟩,
    hOdis,hinc,hBdis,hBsub,hfront,hW,hcenter,hopen,hS,hSC,hnest,?_⟩
  intro j hji
  apply disjoint_left.mpr
  intro x hxD hxO
  rcases ((hO j).2.2.2 hxO).1.1 with hxold | hxoff
  · exact disjoint_left.mp (hdis₀ hji) (hnest j hxO) (subset_closure hxold)
  · exact hxoff hxD

end PoincareConjecture.M76
