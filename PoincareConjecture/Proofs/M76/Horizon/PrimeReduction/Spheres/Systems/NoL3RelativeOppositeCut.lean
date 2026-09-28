import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalRelativeCenteredCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeSingleCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.HalfCollarAttachment









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.original_relative_opposite_collar_cut
    {X E A A₀ ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [TopologicalSpace A₀]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R S K O₀ : Set X} (s : ChartwisePLSphere e S)
    (hR : IsCompact R) (he : PLDomain e R)
    (W₀ : (A₀ × unitInterval) ≃ₜ closure O₀) (hCR₀ : closure O₀ ⊆ interior R)
    (hO₀ : ∀ z, (W₀ z : X) ∈ O₀ ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS₀ : ∀ z, (W₀ z : X) ∈ S ↔ (z.2 : ℝ) = 1/2) (hSC₀ : S ⊆ closure O₀)
    (hQ₀ : IsCompact (R \ O₀)) (hQ₀PL : PLDomain e (R \ O₀))
    (B₀ : Bool → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure O₀)
    (hfront₀ : frontier (R \ O₀) = frontier R ∪ ⋃ i, B₀ i)
    (hno : HasNoPuncturedSphereComponents e f (R \ O₀))
    (F : X → A) (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F S) {N : Set A} (hN : N = F '' S)
    (hNc : IsCompact N) (hNconn : IsConnected N)
    (c : A × ℝ → X) (hc : PolyhedralPLInCharts e c (N ×ˢ Icc (-1 : ℝ) 1))
    (hi : InjOn c (N ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1)
    (hinside : MapsTo c (N ×ˢ Icc (-ε) ε) (O₀ ∩ interior R))
    (hopen : IsOpen (c '' (N ×ˢ Ioo (-ε) ε)))
    (hzero : S = c '' (N ×ˢ ({0} : Set ℝ))) (positive : Bool)
    (hKi : interior K = c '' (N ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε)))
    (hKPL : PLDomain e K) (hKR : K ⊆ interior R)
    (BK : Bool → Set X) (sBK : ∀ i, ChartwisePLSphere e (BK i))
    (hKfront : frontier K = BK false ∪ BK true)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    HasNoPuncturedSphereComponents e f (R ∩ (interior K)ᶜ) := by
  let O := c '' (N ×ˢ Ioo (-ε) ε)
  obtain ⟨B,sB,W,hQ,hQPL,hBdis,hBsub,hOf,hBfront,hCR,hWO,hWS,hSC⟩ :=
    s.original_relative_centered_collar_cut hR he F hF hFi hN hNc c hc hi hε hεsmall
      (fun z hz => (hinside hz).2) hopen hzero
  have hnew : HasNoPuncturedSphereComponents e f (R \ O) := by
    apply hno.mono_relative_single_collar R S O₀ O W₀ W hQ₀ hQ₀PL hQ hQPL hCR₀ hCR
      hO₀ hWO hS₀ hWS hSC₀ hSC ?_ B₀ B sB₀ sB hB₀dis hB₀sub hBsub
      hfront₀ hBfront L g hg hgi hreal
    rintro x ⟨z,hz,rfl⟩
    exact (hinside ⟨hz.1,hz.2.1.le,hz.2.2.le⟩).1
  let D := c '' (N ×ˢ (if positive then Icc 0 ε else Icc (-ε) 0))
  obtain ⟨heq,hD,_,hcontact⟩ := half_collar_attachment hNconn R c hc.continuousOn hi
    hε hεsmall.le (fun z hz => interior_subset (hinside hz).2) positive
  have hEq : R \ interior K = (R \ O) ∪ D := by
    rw [hKi]
    exact heq
  obtain ⟨hQh,hQhPL,_,_,hQhf⟩ := he.interior_removal_geometry hR hKPL hKR
  change frontier (R \ interior K) = frontier K ∪ frontier R at hQhf
  have hQhfront : frontier (R \ interior K) = frontier R ∪ ⋃ b, BK b := by
    rw [hQhf,hKfront]
    ext x
    simp only [mem_union,mem_iUnion,Bool.exists_bool]
    tauto
  have hFB : Disjoint (frontier R) (⋃ b, B b) := by
    apply disjoint_left.mpr
    intro x hx hb
    obtain ⟨b,hb⟩ := mem_iUnion.mp hb
    exact hx.2 (hCR (hBsub b hb))
  have hFBK : Disjoint (frontier R) (⋃ b, BK b) := by
    apply disjoint_left.mpr
    intro x hx hb
    obtain ⟨b,hb⟩ := mem_iUnion.mp hb
    have hxK : x ∈ frontier K := by
      apply hKfront.symm.subset
      cases b
      · exact Or.inl hb
      · exact Or.inr hb
    exact hx.2 (hKR (hKPL.closed.frontier_subset hxK))
  change IsCompact (R \ interior K) at hQh
  change PLDomain e (R \ interior K) at hQhPL
  rw [hEq] at hQh hQhPL hQhfront
  have hh := hnew.union_relative_connected_attachment hQ hQPL hQh hQhPL isClosed_frontier
    B sB hBdis hFB hBfront BK sBK hFBK hQhfront hD.isPreconnected hcontact L g hg hgi
    (fun x hx => hreal x (hEq.symm.subset hx).1)
  change HasNoPuncturedSphereComponents e f (R \ interior K)
  rwa [hEq]

end PoincareConjecture.M76
