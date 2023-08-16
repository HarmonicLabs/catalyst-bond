import { PAddress, PBool, PByteString, PCurrencySymbol, PDelayed, PExtended, POutputDatum, PScriptContext, PScriptPurpose, PString, PTokenName, PTxInInfo, PTxInfo, PTxOut, PTxOutRef, PUnit, PUpperBound, PValidatorHash, Script, Term, TermFn, UtilityTermOf, bool, bs, compile, data, fn, int, list, pBSToData, pBool, pByteString, pIntToData, pStr, pblake2b_256, pdelay, peqBs, perror, pfn, phead, phoist, pif, pisEmpty, plam, plet, pmakeUnit, pmatch, precursive, pserialiseData, pstruct, ptrace, ptraceError, ptraceIfFalse, punBData, punConstrData, punsafeConvertType, unit } from "@harmoniclabs/plu-ts";
import { plovelaces } from "./utils/PValue/pvalueOf";

const Datum = pstruct({
    /**
     * Rewards to be distributed on lock
     * 
     * (one of these utxos is sufficient but there might be multiple for parallelization00)
    **/
    Allocation: {},
    /**
     * Founds locked by user + assigned rewards
     * (only withdrawable after deadline)
     */
    Rewarded: {
        userAddress: PAddress.type
    }
});

const Rdmr = pstruct({
    /**
     * only used with `Alloacation` datum
     */
    Deposit: {
        contractInputIdx: int, // either 0 or 1
    },
    Withdraw:{}
});

const untyped_contract = pfn([
    PAddress.type,
    int, // deadline (catalyst snapshot)
    // ----------------------- contract ----------------------- //
    Datum.type,
    Rdmr.type,
    PScriptContext.type
],  unit)
(( 
    issuerAddress,
    deadline,
    datum, rdmr, ctx
) => {

    const { tx, purpose } = ctx;

    const spendingUtxoRef = plet(
        pmatch( purpose )
        .onSpending( ({ utxoRef }) => utxoRef )
        ._( _ => perror( PTxOutRef.type ) )
    );

    const extendedToFinite = phoist(
        pfn([ PExtended.type ], int )
        ( extended =>
            pmatch( extended )
            .onPFinite(({ _0 }) => _0 )
            ._( _ => perror( int ) ) 
        )
    );
        

    return pif( unit ).$(

        pmatch( datum )
        .onAllocation( _ => 
            pmatch( rdmr )
            // user is locking
            // allocating rewards
            // (only works before deadline)
            .onDeposit( ({ contractInputIdx }) => {

                // inlined
                const txMaxTime = extendedToFinite.$( tx.interval.to.bound );
    
                // inlined
                const beforeDeadline = txMaxTime.ltEq(
                    deadline.sub( 3600 ) // 1h before deadline
                );

                const contractInIsFst = plet(
                    contractInputIdx.eq( 0 )
                );

                // inlined
                const onlyTwoIns = pisEmpty.$( tx.inputs.tail.tail );

                const _contractInput = plet(
                    pif( PTxInInfo.type ).$( contractInIsFst )
                    .then( tx.inputs.head )
                    .else( tx.inputs.tail.head )
                );

                // inlined
                const contractInIsValid = _contractInput.utxoRef.eq( spendingUtxoRef );

                const contractInput = plet( _contractInput.resolved );

                const contractAddress = contractInput.address;

                const userInput = plet(
                    pif( PTxOut.type ).$( contractInIsFst )
                    .then( tx.inputs.tail.head.resolved )
                    .else( tx.inputs.head.resolved )
                );

                const userAddress = userInput.address;

                const contractLovelaces = plet(
                    plovelaces.$( contractInput.value )
                );

                const userLovelaces = plet(
                    plovelaces.$( userInput.value )
                );

                const fee = plet(
                    plovelaces.$( tx.fee )
                );

                // for every 1000 ADA there is 1 ADA of interest (40% APY)
                // change this formula if you don't like it
                const interests = plet( userLovelaces.div( 1_000 ) );

                const expectedUserOutLovelaces = plet(
                    userLovelaces
                    .add( interests )
                    .sub( fee )
                );

                const expectedContractOutLovelaces = plet(
                    contractLovelaces.sub( interests )
                );

                // inlined
                const onlyTwoOuts = pisEmpty.$( tx.outputs.tail.tail );

                const fstOut = plet( tx.outputs.head );
                const sndOut = plet( tx.outputs.tail.head );

                const isCorrectOut = plet(
                    pfn([
                        PTxOut.type,
                        int,
                        data
                    ], bool )
                    (( 
                        out, 
                        expectedLovelaces, 
                        expectedDatum
                    ) => {

                        const outToThisAddr = out.address.eq( contractAddress );
                        const correctLovelaces = 
                            plovelaces.$( out.value )
                            .eq( expectedLovelaces );

                        const correctDatum = out.datum.eq(
                            POutputDatum.InlineDatum({
                                datum: expectedDatum
                            })
                        )

                        return outToThisAddr.and( correctLovelaces ).and( correctDatum );
                    })
                );

                const isCorrectContractOut = plet(
                    pfn([ PTxOut.type ], bool)
                    ( out =>
                        isCorrectOut
                        .$( out )
                        .$( expectedContractOutLovelaces )
                        .$(
                            punsafeConvertType(
                                Datum.Allocation({}),
                                data
                            )
                        ) 
                    )
                );
                const isCorrectUserOut = plet(
                    pfn([ PTxOut.type ], bool)
                    ( out =>
                        isCorrectOut
                        .$( out )
                        .$( expectedUserOutLovelaces )
                        .$(
                            punsafeConvertType(
                                Datum.Rewarded({
                                    userAddress: PAddress.toData( userAddress )
                                }),
                                data
                            )
                        ) 
                    )
                );

                const correctOuts = onlyTwoOuts.and(
                    pif( bool ).$(
                        isCorrectContractOut.$( fstOut )
                    )
                    .then( isCorrectUserOut.$( sndOut ) )
                    .else(
                        isCorrectUserOut.$( fstOut )
                        .and( isCorrectContractOut.$( sndOut ) )
                    )
                )

                return beforeDeadline
                .and(  onlyTwoIns )
                .and(  contractInIsValid )
                .and(  correctOuts )
            })
            // issuer is withdrawing any founds left
            .onWithdraw( _ => {
    
                // inlined
                const allOutsToIssuer = tx.outputs.every(
                    out => out.address.eq( issuerAddress )
                );
    
                // inlined
                // we dont want any possible user sending founds out the contract
                const signedByIssuer = plet(
                    punBData.$( issuerAddress.credential.raw.fields.head )
                ).in( issuerPKh =>
                    tx.signatories.some( issuerPKh.eqTerm )
                );
    
                return allOutsToIssuer.and( signedByIssuer );
            })
        )
        .onRewarded(({ userAddress }) =>
            pmatch( rdmr )
            // no reason to re-deposit a locked utxo 
            .onDeposit(  _ => perror( bool ) )
            // unlock past catalyst snapshot
            .onWithdraw( _ => {

                // inlined
                const txMinTime = extendedToFinite.$( tx.interval.from.bound );

                // inlined
                const pastDeadline = txMinTime.gtEq(
                    deadline.add( 24 * 3600 ) // 1d after deadline
                );

                const singleIn = pisEmpty.$( tx.inputs.tail );

                const singleOut = pisEmpty.$( tx.outputs.tail );

                const out = tx.outputs.head;

                const outToUserAddr = out.address.eq( userAddress );

                return pastDeadline
                .and( singleIn )
                .and( singleOut )
                .and( outToUserAddr )
            }) 
        )
    )
    .then( pmakeUnit() )
    .else( perror( unit ) );
});