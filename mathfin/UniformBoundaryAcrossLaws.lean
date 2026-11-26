import HestonBoundaryBirth

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- The backward conditional mean coefficient is uniform over all
probability laws with the same first-moment bound and affine data. -/
theorem uniform_affine_boundary_backward_mean
    {Ω : Type*} [MeasurableSpace Ω] {α κ a lo hi b B D : ℝ}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a)
    (hlo : 0<lo) (hB : 0≤B) :
    ∃ p ∈ Ioo (2*α-1) α, ∃ C : ℝ, 0<C ∧
      ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] {V : ℝ → Ω → ℝ} {w : ℕ → ℝ → ℝ},
        (∀ t, Measurable (V t)) → (∀ t ω,0≤V t ω) →
        (∀ t∈Icc 0 hi, Integrable (V t) μ) →
        (∀ t∈Icc 0 hi, (∫ ω,V t ω ∂μ)≤B) →
        (∀ (n : ℕ) (t : ℝ), PointChargeRiccatiOn α (n:ℝ) (-κ) (-a) t (w n)) →
        (∀ t∈Icc lo hi, ∀ n, Real.exp (-D) ≤ (∫ ω,laplaceBoundaryWeight (V t) n ω ∂μ)) →
        (∀ t∈Icc lo hi, ∀ n,
          let f (r : ℝ) := ∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n
          ContinuousOn f (Ico 0 t) ∧
          ∀ s ∈ Ioo (0:ℝ) t, f s = f 0+
            volterraConvolution (fractionalK α) (fun r => b-(κ+2*a*w n (t-r))*f r) s) →
        ∀ t ∈ Icc lo hi, ∀ u ∈ Ioc (0:ℝ) t,
          (∫ ω,V (t-u) ω ∂boundaryConditionedMeasure μ {ω | V t ω=0})≤C*u^p := by
  obtain ⟨p,hp,hpg⟩ := exists_backwardPowerCoefficient_gap hα hα' ha
  have hp₀ : 0<p := (show 0<2*α-1 by linarith).trans hp.1
  have hpc : caputoCoefficient α p < boundaryCoefficient α := by
    rw [← two_mul_singularRiccatiCoefficient hα' ha]
    exact hpg
  obtain ⟨c,hc,d,hd,N,hN,hR⟩ :=
    exists_global_riccati_uniform_boundary_lower hα hα' ha hκ (half_pos hlo) hpc
  let K := B/Real.exp (-D)
  have hK : 0≤K := div_nonneg hB (Real.exp_pos _).le
  obtain ⟨A,hA,hComp⟩ := caputo_mean_le_backwardPower_of_volterra (b := b) hα hα' hp₀ hp.2 hc hK hd.1
  let C := max A (K/d^p)
  have hC : 0<C := hA.trans_le (le_max_left _ _)
  refine ⟨p,hp,C,hC,?_⟩
  intro μ _ V w hVm hVnn hVi hVB hw hAff hMean t ht u hu
  let f (n : ℕ) (r : ℝ) := ∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n
  have hdt : d<t := hd.2.trans_lt ((half_lt_self hlo).trans_le ht.1)
  have ht₀ : 0<t := hlo.trans_le ht.1
  have hKf (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 t) : f n r ≤ K := by
    have hr' : r∈Icc 0 hi := ⟨hr.1,hr.2.trans ht.2⟩
    let P := laplaceBoundaryWeight (V t) n
    have hPm : Measurable P := ((hVm t).const_mul (-(n:ℝ))).exp
    have hP0 (ω : Ω) : 0≤P ω := (Real.exp_pos _).le
    have hP1 (ω : Ω) : P ω≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (hVnn _ _))
    have hInt : Integrable (fun ω => P ω*V r ω) μ :=
      (hVi r hr').bdd_mul hPm.aestronglyMeasurable
        (ae_of_all _ fun ω => by simpa only [Real.norm_of_nonneg (hP0 ω)] using hP1 ω)
    have hNum : (∫ ω,P ω*V r ω ∂μ)≤B :=
      (integral_mono hInt (hVi r hr') (fun ω => mul_le_of_le_one_left (hVnn _ _) (hP1 ω))).trans
        (hVB r hr')
    have hPos : 0<(∫ ω,P ω ∂μ) := (Real.exp_pos _).trans_le (hAff t ht n)
    change (∫ ω,V r ω ∂laplaceBoundaryTilt μ (V t) n)≤K
    rw [laplaceBoundaryTilt_integral _ _ (hVm t)]
    exact (div_le_div_of_nonneg_right hNum hPos.le).trans
      (div_le_div_of_nonneg_left hB (Real.exp_pos _) (hAff t ht n))
  have hAtom : 0<μ {ω | V t ω=0} := by
    have hh := ge_of_tendsto (tendsto_laplaceBoundary_atom (hVm t) (ae_of_all _ (hVnn t)))
      (Eventually.of_forall (hAff t ht))
    exact (ENNReal.toReal_pos_iff.mp ((Real.exp_pos _).trans_le hh)).1
  have htu : t-u∈Icc (0:ℝ) t := ⟨sub_nonneg.mpr hu.2,sub_le_self _ hu.1.le⟩
  apply boundaryConditionalMean_le_of_laplaceTilt (hVm t) (ae_of_all _ (hVnn t))
    (hVi (t-u) ⟨htu.1,htu.2.trans ht.2⟩) hAtom
  by_cases hud : d≤u
  · exact Eventually.of_forall fun n => (hKf n (t-u) htu).trans (by
      have hdPow : 0<d^p := Real.rpow_pos_of_pos hd.1 _
      have hPow : d^p≤u^p := Real.rpow_le_rpow hd.1.le hud hp₀.le
      calc
        K = (K/d^p)*d^p := (div_mul_cancel₀ _ hdPow.ne').symm
        _ ≤ C*d^p := mul_le_mul_of_nonneg_right (le_max_right _ _) hdPow.le
        _ ≤ C*u^p := mul_le_mul_of_nonneg_left hPow hC.le)
  · have hPow : 0<u^(2*α-1) := Real.rpow_pos_of_pos hu.1 _
    obtain ⟨n₀,hn₀⟩ := exists_nat_ge ((N:ℝ)/u^(2*α-1))
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hnR : (N:ℝ)≤(n:ℝ)*u^(2*α-1) :=
      (div_le_iff₀ hPow).mp (hn₀.trans (Nat.cast_le.mpr hn))
    let k (r : ℝ) := κ+2*a*w n (t-r)
    have hkc (r : ℝ) (hr : r∈Ico 0 t) : ContDiffAt ℝ 1 k r :=
      contDiffAt_const.add (contDiffAt_const.mul ((hw n t).contDiffAt_pos _ (sub_pos.mpr hr.2)
        |>.comp r (contDiffAt_const.sub contDiffAt_id)))
    have hkC : ContinuousOn k (Ico 0 t) := fun r hr => (hkc r hr).continuousAt.continuousWithinAt
    have hkl (r : ℝ) (hr : r ∈ Icc (t-d) (t-u)) : c*(t-r)^(-α)≤k r := by
      have h₁ : u≤t-r := by linarith [hr.2]
      have h₂ : t-r≤d := by linarith [hr.1]
      have hh := hR hu.1 h₁ h₂ hnR (hw n (t-r))
      dsimp [k]
      linarith
    have hmean := hMean t ht n
    have hh := hComp (T := t) (S := t-u) hdt (sub_lt_self _ hu.1)
      hmean.1 hkC (fun r hr => hkc r ⟨hr.1.le,hr.2⟩)
      (fun r hr => hKf n r ⟨hr.1,hr.2.trans (sub_le_self _ hd.1.le)⟩)
      hkl hmean.2 (t-u) ⟨sub_le_sub_left (le_of_not_ge hud) _,le_rfl⟩
    have hh' : f n (t-u) < A*u^p := by
      simpa only [sub_sub_cancel] using hh
    exact hh'.le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hu.1.le _))

/-- The boundary constants are chosen before the probability law and
filtration when the variance has a common second-moment bound. -/
theorem uniform_heston_zero_boundary_over_laws
    {Ω : Type*} {m : MeasurableSpace Ω}
    {α κ a b v₀ lo hi B₂ : ℝ} {U : ℝ≥0}
    (hα : 1/2<α) (hα' : α<1) (hκ : 0≤κ) (ha : 0<a) (hb : 0≤b) (hv₀ : 0≤v₀)
    (hlo : 0<lo) (hhi : hi<(U:ℝ)) (hB₂ : 0≤B₂) :
    ∃ c C₁ η h₀ : ℝ, 0<c ∧ 0<C₁ ∧ 0<η ∧ 0<h₀ ∧
      ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℝ≥0 m)
        {M V C : ℝ≥0 → Ω → ℝ},
        HestonBoundaryProcess μ 𝒢 U α κ a b v₀ M V C →
        (∀ t≤U, (∫ ω,(V t ω)^2 ∂μ)≤B₂) →
        ∀ t∈Icc lo hi,
          c≤μ.real {ω | V t.toNNReal ω=0} ∧
          ∀ h∈Ioc (0:ℝ) h₀,
            (@boundaryConditionedMeasure Ω m μ {ω | V t.toNNReal ω=0}).real
              {ω | 0<V (t+h).toNNReal ω}≤C₁*h^η := by
  let _ : MeasurableSpace Ω := m
  let j (r : ℝ) := b+v₀*fractionalL α r
  let W := singularRiccatiCoefficient α a
  let D := W*Real.Gamma (1-α)*
    (b*(hi^(1-α)/Real.Gamma (2-α))+v₀*(lo^(1-2*α)/Real.Gamma (2-2*α)))
  let c := Real.exp (-D)
  let h₀ := min 1 ((U:ℝ)-hi)
  have hα₀ : 0<α := by linarith
  have hW : 0<W := singularRiccatiCoefficient_pos hα hα' ha
  have hc : 0<c := Real.exp_pos _
  have hh₀ : 0<h₀ := lt_min zero_lt_one (sub_pos.mpr hhi)
  obtain ⟨w,hw,hwn⟩ := exists_boundary_point_test_family hα hα' hκ ha.le
  have hjm : Measurable j := ((fractionalL_measurable α).const_mul v₀).const_add b
  let B := 1+B₂
  have hB : 0≤B := add_nonneg zero_le_one hB₂
  obtain ⟨p,hp,C₀,hC₀,hBackAll⟩ := uniform_affine_boundary_backward_mean
    (Ω := Ω) (hi := hi) (b := b) (D := D) hα hα' hκ ha hlo hB
  let η := p+1-2*α
  have hη : 0<η := by dsimp [η]; linarith [hp.1]
  have hp₀ : 0<p := by linarith [hp.1]
  let J := j lo
  have hJb {r : ℝ} (hr : lo≤r) : 0≤j r ∧ j r≤J := by
    have hr₀ : 0<r := hlo.trans_le hr
    have hΓ : 0<Real.Gamma (1-α) := Real.Gamma_pos_of_pos (sub_pos.mpr hα')
    have hL₀ : 0≤fractionalL α r := by
      rw [fractionalL,ite_eq_right (not_le.mpr hr₀)]
      exact div_nonneg (Real.rpow_nonneg hr₀.le _) hΓ.le
    have hL : fractionalL α r≤fractionalL α lo := by
      rw [fractionalL,fractionalL,ite_eq_right (not_le.mpr hr₀),ite_eq_right (not_le.mpr hlo)]
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hlo hr (neg_nonpos.mpr hα₀.le)) hΓ.le
    exact ⟨add_nonneg hb (mul_nonneg hv₀ hL₀),
      add_le_add (le_refl b) (mul_le_mul_of_nonneg_left hL hv₀)⟩
  have hJ : 0≤J := (hJb (le_refl lo)).1
  let K := α/Real.Gamma (1-α)
  let E := ∫ u in Ioi (0:ℝ),(1+u)^(-(1+α))*u^p
  let F := Real.Gamma (1+p-α)*Real.Gamma (1-α)/Real.Gamma (2+p-2*α)
  let C₁ := max 1 (2*W*(J+K*C₀*E)*F)
  have hC₁ : 0<C₁ := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨c,C₁,η,h₀,hc,hC₁,hη,hh₀,?_⟩
  intro μ _ 𝒢 M V C hP hSecond
  let v (t : ℝ) := V t.toNNReal
  have hVm (r : ℝ) : Measurable (v r) := ((hP.variance_adapted r.toNNReal).mono (𝒢.le _)).measurable
  have hVn (r : ℝ) (ω : Ω) : 0≤v r ω := hP.variance_nonnegative _ _
  have hVc (ω : Ω) : Continuous (fun r => v r ω) :=
    (hP.variance_continuous ω).comp continuous_real_toNNReal
  have hvTime (r : ℝ) (hr : r∈Icc (0:ℝ) hi) : r.toNNReal≤U :=
    NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal r hr.1] using hr.2.trans hhi.le)
  have hvInt (r : ℝ) (hr : r∈Icc (0:ℝ) hi) : Integrable (v r) μ :=
    hP.variance_integrable _ (hvTime r hr)
  have hvB (r : ℝ) (hr : r∈Icc (0:ℝ) hi) : (∫ ω,v r ω ∂μ)≤B := by
    have hSq := hP.variance_second_integrable _ (hvTime r hr)
    have hi : Integrable (fun _ : Ω => (1:ℝ)) μ := integrable_const _
    have he := integral_mono (hvInt r hr) (hi.add hSq) (fun ω => by
      change v r ω≤1+(v r ω)^2
      nlinarith [sq_nonneg (v r ω-1)])
    have hAdd := integral_add hi hSq
    simp only [Pi.add_apply] at he
    rw [hAdd,integral_const,probReal_univ,one_smul] at he
    exact he.trans (add_le_add (le_refl 1) (hSecond _ (hvTime r hr)))
  have hMeanNorm (t : ℝ) (ht : t∈Icc lo hi) (n : ℕ) :
      (∫ ω,laplaceBoundaryWeight (v t) n ω ∂μ)=Real.exp (-(volterraConvolution (w n) j t)) ∧
      (let f (r : ℝ) := ∫ ω,v r ω ∂laplaceBoundaryTilt μ (v t) n
       ContinuousOn f (Ico (0:ℝ) t) ∧ ∀ s∈Ioo (0:ℝ) t, f s=f 0+
         volterraConvolution (fractionalK α) (fun r => b-(κ+2*a*w n (t-r))*f r) s) := by
    have ht₀ : 0<t := hlo.trans_le ht.1
    have he := heston_boundary_tilt_mean hα hα' hκ ha.le hb hv₀
      (Real.toNNReal_pos.mpr ht₀) (hvTime t ⟨ht₀.le,ht.2⟩) hP
      (by simpa only [Real.coe_toNNReal t ht₀.le] using hw n t) (hwn n)
    simpa only [v,j,Real.coe_toNNReal t ht₀.le] using he
  have hUpper (t : ℝ) (ht : t∈Icc lo hi) (n : ℕ) : volterraConvolution (w n) j t ≤ D :=
    point_riccati_input_convolution_uniform hα hα' hκ ha hlo ht hb hv₀ (hw n t)
  have hAff (t : ℝ) (ht : t∈Icc lo hi) (n : ℕ) :
      Real.exp (-D)≤(∫ ω,laplaceBoundaryWeight (v t) n ω ∂μ) := by
    rw [(hMeanNorm t ht n).1]
    exact Real.exp_le_exp.mpr (neg_le_neg (hUpper t ht n))
  have hBack := hBackAll μ hVm hVn hvInt hvB hw hAff (fun t ht n => (hMeanNorm t ht n).2)
  intro t ht
  have ht₀ : 0<t := hlo.trans_le ht.1
  let Z := {ω | v t ω=0}
  obtain ⟨hCZ,hZ⟩ := laplaceBoundary_atom_of_affine_bound (hVm t) (ae_of_all _ (hVn t))
    (fun n => (hMeanNorm t ht n).1) (hUpper t ht)
  refine ⟨hCZ,?_⟩
  intro h hh
  have h₁ : h≤1 := hh.2.trans (min_le_left _ _)
  have hth : t+h≤(U:ℝ) := by
    linarith [ht.2,hh.2.trans (min_le_right 1 ((U:ℝ)-hi))]
  have hTh : 0<t+h := add_pos ht₀ hh.1
  let H := (t+h).toNNReal
  let S := t.toNNReal
  have hH : H≤U := NNReal.coe_le_coe.mp (by simpa only [H,Real.coe_toNNReal _ hTh.le] using hth)
  have hSH : S<H := NNReal.coe_lt_coe.mp (by
    simpa only [H,S,Real.coe_toNNReal _ hTh.le,Real.coe_toNNReal _ ht₀.le] using lt_add_of_pos_right t hh.1)
  let Q := boundaryConditionedMeasure μ Z
  let : IsProbabilityMeasure Q := boundaryConditionedMeasure_isProbability hZ
  have hZmeas : MeasurableSet[𝒢 S] Z := measurableSet_eq_fun (hP.variance_adapted S).measurable measurable_const
  have hZreal : 0<μ.real Z := hc.trans_le hCZ
  have hQvi (r : ℝ) (hr : r∈Ioc (0:ℝ) t) : Integrable (v r) Q :=
    ((hvInt r ⟨hr.1.le,hr.2.trans ht.2⟩).restrict).smul_measure (ENNReal.inv_ne_top.mpr hZ.ne')
  have hQvb (r : ℝ) (hr : r∈Ioc (0:ℝ) t) : (∫ ω,‖v r ω‖ ∂Q)≤B/c := by
    simp_rw [Real.norm_of_nonneg (hVn r _)]
    rw [integral_boundaryConditionedMeasure]
    have hN := setIntegral_le_integral (s := Z) (hvInt r ⟨hr.1.le,hr.2.trans ht.2⟩) (ae_of_all _ (hVn r))
    exact (div_le_div_of_nonneg_right (hN.trans (hvB r ⟨hr.1.le,hr.2.trans ht.2⟩)) hZreal.le).trans
      (div_le_div_of_nonneg_left hB hc hCZ)
  let Ψ (n : ℕ) (ω : Ω) := affineFuturePayoff α (w n) j (fun r => v r ω) (t+h) t
  have hΨ (n : ℕ) : Integrable (Ψ n) Q ∧ (∫ ω,Ψ n ω ∂Q)≤C₁*h^η := by
    have hwp (r : ℝ) (hr : r∈Ioo (0:ℝ) h) : 0≤w n r ∧ w n r≤W*r^(-α) := by
      refine ⟨hwn n r hr.1,?_⟩
      let u := hw n (t+h)
      have hrT : r∈Ioc (0:ℝ) (t+h) := ⟨hr.1,by linarith [hr.2]⟩
      have hC := point_charge_riccati_lt_singular_profile hα hα' hκ ha hTh
        u.measurable u.contDiffAt_pos u.volterra u.asymptotic r hrT
      rw [singularRiccatiProfile,ite_eq_left hr.1] at hC
      exact hC.le
    obtain ⟨hi,he⟩ := affine_future_payoff_mean_bound hα₀ hα' hp₀ hp.2 hη ht₀.le hh.1 h₁
      hC₀.le hJ hW.le hVm hVc hVn hQvi hQvb (hBack t ht) hjm
      (fun y hy => hJb (by linarith [ht.1,hy.1])) (hw n (t+h)).measurable hwp
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hh.1.le _)
  have hA (n : ℕ) : μ[laplaceBoundaryWeight (V H) n | 𝒢 S] =ᵐ[μ] fun ω => Real.exp (-Ψ n ω) := by
    have hh' := heston_boundary_conditional_point_test hα hα' ha.le hb hv₀ hH hSH hP
      (by simpa only [H,Real.coe_toNNReal _ hTh.le] using hw n (t+h)) (hwn n)
    have hLap : laplaceBoundaryWeight (V H) n = fun ω => Real.exp (-((n:ℝ)*V H ω)) := by
      funext ω
      simp only [laplaceBoundaryWeight,neg_mul]
    rw [hLap]
    simpa only [Ψ,v,j,H,S,Real.coe_toNNReal _ ht₀.le,
      Real.coe_toNNReal _ hTh.le] using hh'
  have hΨi (n : ℕ) : Integrable (Ψ n) (μ.restrict Z) :=
    (integrable_smul_measure (ENNReal.inv_ne_zero.mpr (measure_ne_top μ Z))
      (ENNReal.inv_ne_top.mpr hZ.ne')).mp (hΨ n).1
  have hΨb (n : ℕ) : (∫ ω in Z,Ψ n ω ∂μ) ≤ (C₁*h^η)*μ.real Z := by
    have hh' := (hΨ n).2
    change (∫ ω,Ψ n ω ∂boundaryConditionedMeasure μ Z)≤_ at hh'
    rw [integral_boundaryConditionedMeasure] at hh'
    exact (div_le_iff₀ hZreal).mp hh'
  exact boundaryConditionalPositive_le_of_affine_bound (𝒢.le S) hZmeas hZ (hVm (t+h))
    (ae_of_all _ (hVn (t+h))) hA hΨi hΨb


#print axioms uniform_affine_boundary_backward_mean
#print axioms uniform_heston_zero_boundary_over_laws

end RoughHeston
