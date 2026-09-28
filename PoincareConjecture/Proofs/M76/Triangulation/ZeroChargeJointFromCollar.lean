import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointSignedImage
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeAnnulusTopology
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLBoundary

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {n : ℕ}

theorem exists_joint_cylinder_of_normalized_polygon_collar
    (P : Polygon V (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P) (hdim : Module.finrank ℝ E = 2)
    {r tau : ℝ} (hr : 0 < r) (htau : 0 < tau)
    (F : V × (ℝ × ℝ) → E × ℝ)
    (hF : FinitePiecewiseAffineOn F
      (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r)))
    (hFinj : InjOn F (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r)))
    (hheight : ∀ p ∈ P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r),
      (F p).2 = p.2.1) {d : Set E} (hd : IsCompact d) :
    ∃ epsilon : ℝ, epsilon ∈ Ioo 0 (min r tau) ∧
      ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ Convex ℝ K.space ∧
        d ⊆ interior K.space ∧
        (∀ v ∈ P.boundary ℝ, (F (v, (0, 0))).1 ∈ interior K.space) ∧
        ∃ e : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) ≃ₜ
            (K.space ×ˢ Icc (-epsilon) epsilon),
          e.IsFinitePL ∧
          (∀ p : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)),
            (e p : E × ℝ).2 = (p : E × ℝ).2) ∧
          (∀ p : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)),
            (p : E × ℝ).2 = 0 → e p = p) ∧
          ∀ (p : (K.space ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)))
            (v : V), v ∈ P.boundary ℝ → (p : E × ℝ).1 = (F (v, (0, 0))).1 →
              (e p : E × ℝ) = F (v, ((p : E × ℝ).2, 0)) := by
  classical
  let B := P.boundary ℝ
  let I : ℝ → Set ℝ := fun s => Icc (-s) s
  let f : V × ℝ → E := fun p => (F (p.1, (0, p.2))).1
  have hzero : (0 : ℝ) ∈ I r := ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hidB : FinitePiecewiseAffineOn (id : V → V) B :=
    ⟨P.simplicialComplex hP, P.finite_simplicialComplex_faces hP,
      P.simplicialComplex_space hP,
      (P.simplicialComplex hP).affineOnFaces_affine (ContinuousAffineMap.id ℝ V)⟩
  have hidprod (s : ℝ) (hs : 0 < s) :
      FinitePiecewiseAffineOn (id : V × ℝ → V × ℝ) (B ×ˢ I s) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (show -s < s by linarith)
    have hidI : FinitePiecewiseAffineOn (id : ℝ → ℝ) (I s) :=
      ⟨J, hJ, hJI, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
    exact hidB.prodMap hidI
  let a : (V × ℝ) →ᴬ[ℝ] (V × (ℝ × ℝ)) :=
    (ContinuousLinearMap.fst ℝ V ℝ).toContinuousAffineMap.prod
      ((ContinuousAffineMap.const ℝ (V × ℝ) (0 : ℝ)).prod
        (ContinuousLinearMap.snd ℝ V ℝ).toContinuousAffineMap)
  have hf (s : ℝ) (hs : 0 < s) (hsr : s ≤ r) :
      FinitePiecewiseAffineOn f (B ×ˢ I s) := by
    have hmap : MapsTo a (B ×ˢ I s) (B ×ˢ (I r ×ˢ I r)) := by
      intro p hp
      exact ⟨hp.1, hzero, (neg_le_neg hsr).trans hp.2.1, hp.2.2.trans hsr⟩
    exact (hF.comp ((hidprod s hs).postcomp a) hmap).postcomp
      (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  have hfi : InjOn f (B ×ˢ I r) := by
    intro p hp q hq heq
    have hp' : (p.1, (0, p.2)) ∈ B ×ˢ (I r ×ˢ I r) := ⟨hp.1, hzero, hp.2⟩
    have hq' : (q.1, (0, q.2)) ∈ B ×ˢ (I r ×ˢ I r) := ⟨hq.1, hzero, hq.2⟩
    have hfull : F (p.1, (0, p.2)) = F (q.1, (0, q.2)) :=
      Prod.ext heq ((hheight _ hp').trans (hheight _ hq').symm)
    have hsource := hFinj hp' hq' hfull
    exact Prod.ext (congrArg (fun u : V × (ℝ × ℝ) => u.1) hsource)
      (congrArg (fun u : V × (ℝ × ℝ) => u.2.2) hsource)
  obtain ⟨G, hG, hGval⟩ := hF.exists_homeomorph_image hFinj
  obtain ⟨g, hg, hgval⟩ := hG.symm
  have hgleft (p : V × (ℝ × ℝ)) (hp : p ∈ B ×ˢ (I r ×ˢ I r)) :
      g (F p) = p := by
    rw [← hGval ⟨p, hp⟩, ← hgval, G.symm_apply_apply]
  let Z : E × ℝ → ℝ := fun p => (g p).2.2
  have hZ : FinitePiecewiseAffineOn Z (F '' (B ×ˢ (I r ×ˢ I r))) :=
    hg.postcomp ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ V (ℝ × ℝ))).toContinuousAffineMap
  obtain ⟨L, hL, hLbound⟩ := exists_transverse_lipschitz hZ
  have htrans : ∀ p ∈ B ×ˢ (I r ×ˢ I r), ∀ q ∈ B ×ˢ (I r ×ˢ I r),
      |p.2.2 - q.2.2| ≤ L * ‖F p - F q‖ := by
    intro p hp q hq
    have h := hLbound (F p) (mem_image_of_mem _ hp) (F q) (mem_image_of_mem _ hq)
    simpa only [Z, hgleft p hp, hgleft q hq] using h
  let R := r / 4
  let W := r / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hRW : R < W := by dsimp [R, W]; linarith
  have hWr : W < r := by dsimp [W]; linarith
  have hRr : R < r := hRW.trans hWr
  let N := f '' (B ×ˢ I W)
  let T := f '' (B ×ˢ I R)
  obtain ⟨hNcompact, hNinterior, hNfrontier, hNconnected⟩ :=
    polygon_collar_annulus_topology P hP hPinj hdim hW hWr (hf r hr le_rfl) hfi
  change IsCompact N at hNcompact
  change IsConnected (interior N) at hNconnected
  have hTcompact : IsCompact T :=
    (P.isCompact_boundary.prod isCompact_Icc).image_of_continuousOn (hf R hR hRr.le).continuousOn
  have hTN : T ⊆ interior N := by
    rw [hNinterior]
    rintro _ ⟨⟨v, z⟩, ⟨hv, hz⟩, rfl⟩
    exact ⟨(v, z), ⟨hv, by linarith [hz.1], by linarith [hz.2]⟩, rfl⟩
  have hwide : B ×ˢ I W ⊆ B ×ˢ I r :=
    prod_mono Subset.rfl (fun _ hz => ⟨(neg_le_neg hWr.le).trans hz.1,
      hz.2.trans hWr.le⟩)
  obtain ⟨b, hb, hbval⟩ := (hf W hW hWr.le).exists_homeomorph_image (hfi.mono hwide)
  obtain ⟨j, hj, hjval⟩ := hb.symm
  change FinitePiecewiseAffineOn j N at hj
  have hjleft (p : V × ℝ) (hp : p ∈ B ×ˢ I W) : j (f p) = p := by
    rw [← hbval ⟨p, hp⟩, ← hjval, b.symm_apply_apply]
  have hjmap : MapsTo j N (B ×ˢ I W) := by
    intro x hx
    rw [← hjval ⟨x, hx⟩]
    exact (b.symm ⟨x, hx⟩).property
  have hjmapr : MapsTo j N (B ×ˢ I r) := fun x hx => hwide (hjmap hx)
  have hjright (x : E) (hx : x ∈ N) : f (j x) = x := by
    rw [← hjval ⟨x, hx⟩, ← hbval, b.apply_symm_apply]
  have hji : InjOn j N := by
    intro x hx y hy heq
    rw [← hjright x hx, ← hjright y hy, heq]
  have hNid : FinitePiecewiseAffineOn (id : E → E) N := by
    obtain ⟨Q, hQ, hQN, _⟩ := hj
    exact ⟨Q, hQ, hQN, Q.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  let epsilon := min (min (r / 2) (tau / 2)) (R / (2 * (L + 1)))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hepsr : epsilon < r :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hepstau : epsilon < tau :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hepsbound : epsilon * (2 * (L + 1)) ≤ R :=
    (le_div_iff₀ (by positivity : 0 < 2 * (L + 1))).mp (min_le_right _ _)
  have hsmall : L * ‖((0 : E), (1 : ℝ))‖ * (epsilon / R) < 1 := by
    have hstrict : L * epsilon < R := by nlinarith
    have hdiv : L * epsilon / R < 1 := (div_lt_one hR).mpr hstrict
    simpa only [Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_one,
      max_eq_right zero_le_one, mul_one, mul_div_assoc] using hdiv
  let H := jointProjectedCutoff F j R epsilon
  have hH : FinitePiecewiseAffineOn H (N ×ˢ I epsilon) :=
    jointProjectedCutoff_finitePiecewiseAffineOn hF hj hjmapr hR hepsilon hepsr.le
  have hHinjection (t : ℝ) : InjOn (fun x => H (x, t)) N :=
    jointProjectedCutoff_injOn hFinj hji hjmapr hheight hL htrans
      hR hepsilon.le hepsr.le hsmall t
  have hHstart (x : E) (hx : x ∈ N) : H (x, 0) = x :=
    jointProjectedCutoff_at_zero hR hepsilon.le hjright hx
  have hHsupport (x : E) (hx : x ∈ N) (hxt : x ∉ T) (t : ℝ) : H (x, t) = x := by
    have hz : R ≤ |(j x).2| := by
      by_contra h
      have hzi : (j x).2 ∈ I R := abs_le.mp (lt_of_not_ge h).le
      exact hxt ⟨j x, ⟨(hjmap hx).1, hzi⟩, hjright x hx⟩
    exact jointProjectedCutoff_fixed_margin hR hepsilon.le hjright hx hz t
  have hHfix (t : ℝ) : EqOn (fun x => H (x, t)) id (frontier N) := by
    intro x hx
    exact hHsupport x (hNcompact.isClosed.frontier_subset hx) (fun h => hx.2 (hTN h)) t
  have hHimage : ∀ t ∈ I epsilon, (fun x => H (x, t)) '' N = N :=
    image_eq_of_signed_joint_finitePL hNid hNconnected hepsilon.le H hH
      (fun t _ => hHinjection t) (fun t _ => hHfix t) (fun x hx => hHstart x hx)
  obtain ⟨K, hK, hKconvex, hNKd⟩ :=
    (hNcompact.union hd).exists_finite_convex_neighborhood
  have hNKint : N ⊆ interior K.space := fun x hx => hNKd (Or.inl hx)
  have hNK : N ⊆ K.space := hNKint.trans interior_subset
  have hdK : d ⊆ interior K.space := fun x hx => hNKd (Or.inr hx)
  have hzeroW : (0 : ℝ) ∈ I W := ⟨neg_nonpos.mpr hW.le, hW.le⟩
  have hcoreN (v : V) (hv : v ∈ B) : (F (v, (0, 0))).1 ∈ N :=
    ⟨(v, 0), ⟨hv, hzeroW⟩, rfl⟩
  obtain ⟨e, he, heheight, heN, _, hestart⟩ :=
    exists_joint_finitePL_cylinder K hK hNK hTcompact hTN
      (show -epsilon < epsilon by linarith) H hH
      (fun p hp hpt => hHsupport p.1 hp.1 hpt p.2)
      (fun t _ => hHinjection t) hHimage 0 hHstart
  refine ⟨epsilon, ⟨hepsilon, lt_min hepsr hepstau⟩,
    K, hK, hKconvex, hdK, (fun v hv => hNKint (hcoreN v hv)),
    e, he, heheight, hestart, ?_⟩
  intro p v hv hpv
  have hpN : (p : E × ℝ).1 ∈ N := hpv.symm ▸ hcoreN v hv
  have hjp : j (p : E × ℝ).1 = (v, 0) := by
    rw [hpv]
    exact hjleft (v, 0) ⟨hv, hzeroW⟩
  rw [heN p hpN]
  apply Prod.ext
  · change (F ((j (p : E × ℝ).1).1,
      (signedTimeCutoff R epsilon (p : E × ℝ).2 (j (p : E × ℝ).1).2,
        (j (p : E × ℝ).1).2))).1 = (F (v, ((p : E × ℝ).2, 0))).1
    rw [hjp, signedTimeCutoff_core hR hepsilon.le p.property.2]
  · exact (hheight (v, ((p : E × ℝ).2, 0))
      ⟨hv, ⟨(neg_le_neg hepsr.le).trans p.property.2.1,
      p.property.2.2.trans hepsr.le⟩, hzero⟩).symm

end PoincareConjecture.M76.ZeroChargeJoint
