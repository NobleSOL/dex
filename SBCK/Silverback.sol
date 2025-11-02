// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.19;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

interface ISilverbackRouter {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

interface ISilverbackFactory {
    function createPair(address tokenA, address tokenB) external returns (address SILVERBACK_PAIR);
}

contract Silverback is IERC20, Ownable {
    /* -------------------------------------------------------------------------- */
    /*                                  constants                                 */
    /* -------------------------------------------------------------------------- */
    address constant DEAD = 0x000000000000000000000000000000000000dEaD;
    address constant ZERO = 0x0000000000000000000000000000000000000000;

    uint256 constant MAX_FEE = 30;

    /* -------------------------------------------------------------------------- */
    /*                                   states                                   */
    /* -------------------------------------------------------------------------- */
    ISilverbackRouter public constant SILVERBACK_ROUTER =
        ISilverbackRouter(0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D);
    address public immutable SILVERBACK_PAIR;

    struct Fee {
        uint8 operations;
        uint8 lp;
        uint128 total;
    }

    string _name = "Silverback";
    string _symbol = "SBCK";

    uint256 _totalSupply = 100_000_000 ether;
    uint256 public _maxTxAmount = _totalSupply * 2 / 100;

    mapping(address => uint256) public _balances;
    mapping(address => mapping(address => uint256)) _allowances;

    bool public limitsEnabled = true;
    mapping(address => bool) isFeeExempt;
    mapping(address => bool) isTxLimitExempt;

    Fee public buyFee = Fee({operations: 10, lp: 10, total: 20});
    Fee public sellFee = Fee({operations: 10, lp: 10, total: 20});

    address private operationsFeeReceiver;
    address private lpFeeReceiver;

    bool public claimingFees = true;
    uint256 public swapThreshold = (_totalSupply * 2) / 1000;
    bool inSwap;

    /* -------------------------------------------------------------------------- */
    /*                                  modifiers                                 */
    /* -------------------------------------------------------------------------- */
    modifier swapping() {
        inSwap = true;
        _;
        inSwap = false;
    }

    /* -------------------------------------------------------------------------- */
    /*                                 constructor                                */
    /* -------------------------------------------------------------------------- */
    constructor() {
        // create silverback pair
        address _silverbackPair =
            ISilverbackFactory(SILVERBACK_ROUTER.factory()).createPair(address(this), SILVERBACK_ROUTER.WETH());
        SILVERBACK_PAIR = _silverbackPair;

        _allowances[address(this)][address(SILVERBACK_ROUTER)] = type(uint256).max;
        _allowances[address(this)][tx.origin] = type(uint256).max;

        isTxLimitExempt[address(this)] = true;
        isTxLimitExempt[address(SILVERBACK_ROUTER)] = true;
        isTxLimitExempt[_silverbackPair] = true;
        isTxLimitExempt[tx.origin] = true;
        isFeeExempt[tx.origin] = true;

        operationsFeeReceiver = 0x083654F6bdA189A91d823940988609382b80236A;
        lpFeeReceiver = 0x69625581af76272Fc1Cad7f6160007f77508572e;

        _balances[tx.origin] = _totalSupply;
        emit Transfer(address(0), tx.origin, _totalSupply);
    }

    receive() external payable {}

    /* -------------------------------------------------------------------------- */
    /*                                    ERC20                                   */
    /* -------------------------------------------------------------------------- */
    function approve(address spender, uint256 amount) public override returns (bool) {
        _allowances[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    function approveMax(address spender) external returns (bool) {
        return approve(spender, type(uint256).max);
    }

    function transfer(address recipient, uint256 amount) external override returns (bool) {
        return _transferFrom(msg.sender, recipient, amount);
    }

    function transferFrom(address sender, address recipient, uint256 amount) external override returns (bool) {
        if (_allowances[sender][msg.sender] != type(uint256).max) {
            require(_allowances[sender][msg.sender] >= amount, "ERC20: insufficient allowance");
            _allowances[sender][msg.sender] = _allowances[sender][msg.sender] - amount;
        }

        return _transferFrom(sender, recipient, amount);
    }

    /* -------------------------------------------------------------------------- */
    /*                                    views                                   */
    /* -------------------------------------------------------------------------- */
    function totalSupply() external view override returns (uint256) {
        return _totalSupply;
    }

    function decimals() external pure returns (uint8) {
        return 18;
    }

    function name() external view returns (string memory) {
        return _name;
    }

    function symbol() external view returns (string memory) {
        return _symbol;
    }

    function balanceOf(address account) public view override returns (uint256) {
        return _balances[account];
    }

    function allowance(address holder, address spender) external view override returns (uint256) {
        return _allowances[holder][spender];
    }

    function getCirculatingSupply() public view returns (uint256) {
        return _totalSupply - balanceOf(DEAD) - balanceOf(ZERO);
    }

    /* -------------------------------------------------------------------------- */
    /*                                   owners                                   */
    /* -------------------------------------------------------------------------- */
    function clearStuckBalance() external onlyOwner {
        (bool success,) = payable(msg.sender).call{value: address(this).balance}("");
        require(success);
    }

    function clearStuckToken() external onlyOwner {
        _transferFrom(address(this), msg.sender, balanceOf(address(this)));
    }

    function setSwapBackSettings(bool _enabled, uint256 _amount) external onlyOwner {
        claimingFees = _enabled;
        swapThreshold = _amount;
    }

    function changeFees(
        uint8 operationsFeeBuy,
        uint8 lpFeeBuy,
        uint8 operationsFeeSell,
        uint8 lpFeeSell
    ) external onlyOwner {
        uint128 __totalBuyFee = operationsFeeBuy + lpFeeBuy;
        uint128 __totalSellFee = operationsFeeSell + lpFeeSell;

        require(__totalBuyFee <= MAX_FEE, "Buy fees too high");
        require(__totalSellFee <= MAX_FEE, "Sell fees too high");

        buyFee = Fee({
            operations: operationsFeeBuy,
            lp: lpFeeBuy,
            total: __totalBuyFee
        });

        sellFee = Fee({
            operations: operationsFeeSell,
            lp: lpFeeSell,
            total: __totalSellFee
        });
    }

    function setIsFeeExempt(address holder, bool exempt) external onlyOwner {
        isFeeExempt[holder] = exempt;
    }

    function setIsTxLimitExempt(address holder, bool exempt) external onlyOwner {
        isTxLimitExempt[holder] = exempt;
    }

    function setFeeReceivers(address o_, address lp_) external onlyOwner {
        operationsFeeReceiver = o_;
        lpFeeReceiver = lp_;
    }

    function setMaxTxBasisPoint(uint256 p_) external onlyOwner {
        _maxTxAmount = _totalSupply * p_ / 10000;
    }

    function setLimitsEnabled(bool e_) external onlyOwner {
        limitsEnabled = e_;
    }

    /* -------------------------------------------------------------------------- */
    /*                                   private                                  */
    /* -------------------------------------------------------------------------- */
    function _transferFrom(address sender, address recipient, uint256 amount) internal returns (bool) {
        if (inSwap) {
            return _basicTransfer(sender, recipient, amount);
        }

        if (limitsEnabled && !isTxLimitExempt[sender] && !isTxLimitExempt[recipient]) {
            require(amount <= _maxTxAmount, "Transfer amount exceeds the maxTxAmount.");
        }

        if (_shouldSwapBack()) {
            _swapBack();
        }

        require(_balances[sender] >= amount, "Insufficient Balance");
        _balances[sender] = _balances[sender] - amount;

        uint256 amountReceived = _shouldTakeFee(sender, recipient)
            ? _takeFee(sender == SILVERBACK_PAIR ? true : false, sender, amount)
            : amount;
        _balances[recipient] = _balances[recipient] + amountReceived;

        emit Transfer(sender, recipient, amountReceived);
        return true;
    }

    function _basicTransfer(address sender, address recipient, uint256 amount) internal returns (bool) {
        require(_balances[sender] >= amount, "Insufficient Balance");
        _balances[sender] = _balances[sender] - amount;
        _balances[recipient] = _balances[recipient] + amount;
        emit Transfer(sender, recipient, amount);
        return true;
    }

    function _takeFee(bool buying, address sender, uint256 amount) internal returns (uint256) {
        Fee memory __buyFee = buyFee;
        Fee memory __sellFee = sellFee;

        uint256 feeAmount = buying == true
            ? amount * __buyFee.total / 100
            : amount * __sellFee.total / 100;

        if (feeAmount > 0) {
            _balances[address(this)] = _balances[address(this)] + feeAmount;
            emit Transfer(sender, address(this), feeAmount);
        }

        return amount - feeAmount;
    }

    function _shouldSwapBack() internal view returns (bool) {
        return msg.sender != SILVERBACK_PAIR && !inSwap && claimingFees && balanceOf(address(this)) >= swapThreshold;
    }

    function _swapBack() internal swapping {
        Fee memory __sellFee = sellFee;

        uint256 __swapThreshold = swapThreshold;
        approve(address(SILVERBACK_ROUTER), __swapThreshold);

        // swap
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = SILVERBACK_ROUTER.WETH();

        SILVERBACK_ROUTER.swapExactTokensForETHSupportingFeeOnTransferTokens(
            __swapThreshold, 0, path, address(this), block.timestamp
        );

        uint256 amountETH = address(this).balance;

        uint256 totalSwapFee = __sellFee.total;
        uint256 amountETHOperations = amountETH * __sellFee.operations / totalSwapFee;
        uint256 amountETHLP = amountETH * __sellFee.lp / totalSwapFee;

        // send
        (bool tmpSuccess,) = payable(operationsFeeReceiver).call{value: amountETHOperations}("");
        (tmpSuccess,) = payable(lpFeeReceiver).call{value: amountETHLP}("");
        tmpSuccess = false;
    }

    function _shouldTakeFee(address sender, address recipient) internal view returns (bool) {
        return !isFeeExempt[sender] && !isFeeExempt[recipient];
    }
}
