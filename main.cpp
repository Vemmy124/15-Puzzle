#include <iostream>
#include <string>
#include <stack>
#include <queue>
#include <unordered_map>
#include <vector>
#include <algorithm>
#include <cassert>

const int SQRT_BOARD_SIZE = 4;
const int BOARD_SIZE = SQRT_BOARD_SIZE * SQRT_BOARD_SIZE;
const int MAX_NUMBER_OF_SUCCESSORS = 4;
const int MAX_DISTANCE = 80;

typedef unsigned long long PositionId;

using std::cin;
using std::cout;
using std::endl;
using std::string;
using std::stack;
using std::queue;
using std::unordered_map;
using std::vector;
using std::min;
using std::max;
using std::pair;
using std::make_pair;
using std::swap;

enum { forward = true, backward = false };
enum { left = -1, right = 1, up = -SQRT_BOARD_SIZE, down = SQRT_BOARD_SIZE };
enum { L, R, U, D };

PositionId PosToInt( int* Position )
{
    PositionId result = 0;
    unsigned long long mult = 1;
    for( int i = BOARD_SIZE - 1; i >= 0; --i ) {
        result += Position[i] * mult;
        mult *= 16;
    }
    return result;
}

void IntToPos( PositionId intPosition, int* Position )
{
    for( int i = BOARD_SIZE - 1; i >= 0; --i ) {
        Position[i] = intPosition % 16;
        intPosition /= 16;
    }
}


int GetPos( int value, int* CurrentPosition )
{
    assert( value >= 0 && value < BOARD_SIZE );
    for( int i = 0; i < BOARD_SIZE; ++i ) {
        if( CurrentPosition[i] == value ) {
            return i;
        }
    }
    assert( false );	// Not expected to get here
    return 0;
}

struct Position
{
    Position( PositionId _position, char _distance, char _manhattan ):
            position( _position ),
            distance( _distance ),
            manhattan( _manhattan )
    {
    }

    PositionId position;
    char distance;
    char manhattan;
};

class Solver
{

public:
    Solver();

    void InitStartPosition( int* Position );
    void InitEndPosition();
    void InitEndPosition( int* Position );
    void TwoWayAStar( int& Distance, string& Route );

private:
    bool IsSolvable();
    void AStarIteration( PositionId endPosition, vector<stack<Position>>& PositionsQ, int& qNumber, int& size, bool Way );
    int ManhattanDistance( PositionId First, PositionId Last );
    int ManhattanChange( PositionId position, char direction, int* EndPosition );
    int RowConflict( int row, int* EndPosition );
    int ColumnConflict( int column, int* EndPosition );
    int CornerConflict( int corner, int by1, int by2, int* EndPosition );
    int LastTurn( int corner, int by1, int by2, int* EndPosition );
    int Conflicts( int* EndPosition );
    int Heuristic( PositionId Position, PositionId endPosition );
    void GetSuccessors( PositionId currentPosition );
    void GetRoute( int& distance, string& Route );
    void GetPreviousRoute( int& distance, string& Route );
    void GetFollowingRoute( int& distance, string& Route );

    PositionId startPosition;
    PositionId endPosition;
    int CurrentPosition[BOARD_SIZE];
    int StartPosition[BOARD_SIZE];
    int EndPosition[BOARD_SIZE];
    unordered_map<PositionId, int> PosToDirWay;
    vector<stack<Position>> PositionsQ1;
    vector<stack<Position>> PositionsQ2;
    int qNumber1;
    int qNumber2;
    int size1;
    int size2;
    PositionId intersection;
    int minDistance;
    PositionId Successors[MAX_NUMBER_OF_SUCCESSORS];
    char Direction[MAX_NUMBER_OF_SUCCESSORS];
    int numberOfSuccessors;
    bool LinearConflicts[BOARD_SIZE];
};

Solver::Solver():
        startPosition( 0 ),
        endPosition( 0 ),
        PositionsQ1( MAX_DISTANCE + 1 ),
        PositionsQ2( MAX_DISTANCE + 1 ),
        qNumber1( 0 ),
        qNumber2( 0 ),
        size1( 0 ),
        size2( 0 ),
        intersection( 0 ),
        minDistance( MAX_DISTANCE + 1 ),
        numberOfSuccessors( 0 )
{
}

bool Solver::IsSolvable()
{
    bool transposition = true;
    for( int i = 0; i < BOARD_SIZE; ++i ) {
        if( StartPosition[i] == 0 ) {
            if( SQRT_BOARD_SIZE == 4 && i / SQRT_BOARD_SIZE % 2 == 0 ) {
                transposition = !transposition;
            }
            continue;
        }
        for( int j = i + 1; j < BOARD_SIZE; ++j ) {
            if( StartPosition[i] > StartPosition[j] && StartPosition[j] != 0 ) {
                transposition = !transposition;
            }
        }
    }
    return transposition;
}

void Solver::InitStartPosition( int* Position )
{
    startPosition = PosToInt( Position );
    IntToPos( startPosition, StartPosition );
}

void Solver::InitEndPosition()
{
    for( int i = 0; i < BOARD_SIZE - 1; ++i ) {
        EndPosition[i] = i + 1;
    }
    EndPosition[BOARD_SIZE - 1] = 0;
    endPosition = PosToInt( EndPosition );
}

void Solver::InitEndPosition( int* Position )
{
    endPosition = PosToInt( Position );
    IntToPos( endPosition, EndPosition );
}

void Solver::GetPreviousRoute( int& distance, string& Route )
{
    PositionId currentPosition = intersection;
    IntToPos( currentPosition, CurrentPosition );
    while( currentPosition != startPosition ) {
        char nextDirection = PosToDirWay[currentPosition] / 16 % 4;
        Route.push_back( nextDirection );
        int zeroPosition = GetPos( 0, CurrentPosition );
        if( currentPosition != startPosition ) {
            if( Route.back() == L ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + 1] );
            } else if( Route.back() == R ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - 1] );
            } else if( Route.back() == U ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + SQRT_BOARD_SIZE] );
            } else if( Route.back() == D ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - SQRT_BOARD_SIZE] );
            }
        }
        currentPosition = PosToInt( CurrentPosition );
        ++distance;
    }
    for( size_t i = 0; i < Route.size() / 2; ++i ) {
        swap( Route[i], Route[Route.size() - 1 - i] );
    }
}

void Solver::GetFollowingRoute( int& distance, string& Route )
{
    PositionId currentPosition = intersection;
    IntToPos( currentPosition, CurrentPosition );
    while( currentPosition != endPosition ) {
        char nextDirection = PosToDirWay[currentPosition] / 4 % 4;
        if( nextDirection == L ) {
            Route.push_back( R );
        } else if( nextDirection == R ) {
            Route.push_back( L );
        } else if( nextDirection == U ) {
            Route.push_back( D );
        } else if( nextDirection == D ) {
            Route.push_back( U );
        }
        int zeroPosition = GetPos( 0, CurrentPosition );
        if( currentPosition != endPosition ) {
            if( Route.back() == L ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - 1] );
            } else if( Route.back() == R ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + 1] );
            } else if( Route.back() == U ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - SQRT_BOARD_SIZE] );
            } else if( Route.back() == D ) {
                swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + SQRT_BOARD_SIZE] );
            }
        }
        currentPosition = PosToInt( CurrentPosition );
        ++distance;
    }
}

void Solver::GetRoute( int& distance, string& Route )
{
    GetPreviousRoute( distance, Route );
    GetFollowingRoute( distance, Route );
}

void Solver::TwoWayAStar( int& distance, string& Route )
{
    distance = 0;

    if( !IsSolvable() ) {
        distance = -1;
        return;
    }

    if( startPosition == endPosition ) {
        distance = 0;
        return;
    }

    PosToDirWay[startPosition] = 2;		// Direction: forward
    PosToDirWay[endPosition] = 1;		// Direction: backward
    int startManhattan = ManhattanDistance( startPosition, endPosition );
    IntToPos( startPosition, CurrentPosition );
    int heuristicDistance1 = startManhattan + Conflicts( EndPosition );
    IntToPos( endPosition, CurrentPosition );
    int heuristicDistance2 = startManhattan + Conflicts( StartPosition );
    PositionsQ1[heuristicDistance1].push( Position( startPosition, 0, startManhattan ) );
    PositionsQ2[heuristicDistance2].push( Position( endPosition, 0, startManhattan ) );
    qNumber1 = heuristicDistance1;
    qNumber2 = heuristicDistance2;
    size1 = size2 = 1;

    while( size1 > 0 || size2 > 0 ) {
        if( size1 < size2 && size1 != 0 || size2 == 0 ) {
            AStarIteration( endPosition, PositionsQ1, qNumber1, size1, forward );
        } else {
            AStarIteration( startPosition, PositionsQ2, qNumber2, size2, backward );
        }
    }
    GetRoute( distance, Route );
    assert( distance == minDistance );
}

int Solver::RowConflict( int row, int* EndPosition )
{
    int returnValue = 0;
    for( int i = 0; i < SQRT_BOARD_SIZE; ++i ) {
        int first = CurrentPosition[row * SQRT_BOARD_SIZE + i];
        if( first == 0 ) {
            continue;
        }
        for( int j = i + 1; j < SQRT_BOARD_SIZE; ++j ) {
            int second = CurrentPosition[row * SQRT_BOARD_SIZE + j];
            if( second == 0 ) {
                continue;
            }
            bool flag = false;
            for( int k = SQRT_BOARD_SIZE - 1; k >= 0; --k ) {
                if( EndPosition[row * SQRT_BOARD_SIZE + k] == first ) {
                    flag = true;
                } else if( flag && EndPosition[row * SQRT_BOARD_SIZE + k] == second ) {
                    LinearConflicts[row * SQRT_BOARD_SIZE + i] = true;
                    LinearConflicts[row * SQRT_BOARD_SIZE + j] = true;
                    returnValue = 2;
                }
            }
        }
    }
    return returnValue;
}

int Solver::ColumnConflict( int column, int* EndPosition )
{
    int returnValue = 0;
    for( int i = 0; i < SQRT_BOARD_SIZE; ++i ) {
        int first = CurrentPosition[column + i * SQRT_BOARD_SIZE];
        if( first == 0 ) {
            continue;
        }
        for( int j = i + 1; j < SQRT_BOARD_SIZE; ++j ) {
            int second = CurrentPosition[column + j * SQRT_BOARD_SIZE];
            if( second == 0 ) {
                continue;
            }
            bool flag = false;
            for( int k = SQRT_BOARD_SIZE - 1; k >= 0; --k ) {
                if( EndPosition[column + k * SQRT_BOARD_SIZE] == first ) {
                    flag = true;
                } else if( flag && EndPosition[column + k * SQRT_BOARD_SIZE] == second ) {
                    LinearConflicts[column + i * SQRT_BOARD_SIZE] = true;
                    LinearConflicts[column + j * SQRT_BOARD_SIZE] = true;
                    returnValue = 2;
                }
            }
        }
    }
    return returnValue;
}

int Solver::CornerConflict( int corner, int by1, int by2, int* EndPosition )
{
    by1 += corner;
    by2 += corner;
    if( EndPosition[corner] != 0
        && !LinearConflicts[corner]
        && CurrentPosition[corner] != EndPosition[corner]
        && ( CurrentPosition[by1] == EndPosition[by1]
             && CurrentPosition[by1] != 0
             && !LinearConflicts[by1]
             && ( CurrentPosition[corner] != 0
                  || CurrentPosition[by2] != EndPosition[corner] )
             || CurrentPosition[by2] == EndPosition[by2]
                && CurrentPosition[by2] != 0
                && !LinearConflicts[by2]
                && ( CurrentPosition[corner] != 0
                     || CurrentPosition[by1] != EndPosition[corner] ) ) ) {
        return 2;
    }
    return 0;
}

int Solver::LastTurn( int corner, int by1, int by2, int* EndPosition )
{
    if( EndPosition[corner] == 0 ) {
        by1 += corner;
        by2 += corner;
        by1 = GetPos( EndPosition[by1], CurrentPosition );
        by2 = GetPos( EndPosition[by2], CurrentPosition );
        if( abs( by1 - corner ) % SQRT_BOARD_SIZE != 0 && abs( by2 - corner ) / SQRT_BOARD_SIZE != 0 ) {
            return 2;
        }
    }
    return 0;
}

int Solver::Conflicts( int* EndPosition )
{
    for( int i = 0; i < BOARD_SIZE; ++i ) {
        LinearConflicts[i] = false;
    }
    int result = 0;
    for( int i = 0; i < SQRT_BOARD_SIZE; ++i ) {
        result += RowConflict( i, EndPosition );
    }
    for( int i = 0; i < SQRT_BOARD_SIZE; ++i ) {
        result += ColumnConflict( i, EndPosition );
    }
    result += CornerConflict( 0, right, down, EndPosition );
    result += CornerConflict( SQRT_BOARD_SIZE - 1, left, down, EndPosition );
    result += CornerConflict( BOARD_SIZE - SQRT_BOARD_SIZE, right, up, EndPosition );
    result += CornerConflict( BOARD_SIZE - 1, left, up, EndPosition );
    result += LastTurn( 0, right, down, EndPosition );
    result += LastTurn( SQRT_BOARD_SIZE - 1, left, down, EndPosition );
    result += LastTurn( BOARD_SIZE - SQRT_BOARD_SIZE, right, up, EndPosition );
    result += LastTurn( BOARD_SIZE - 1, left, up, EndPosition );
    return result;
}

int Solver::ManhattanDistance( PositionId First, PositionId Second )
{
    int result = 0;
    IntToPos( First, CurrentPosition );
    int CurrentPosition2[BOARD_SIZE];
    IntToPos( Second, CurrentPosition2 );
    for( int i = 0; i < BOARD_SIZE; ++i ) {
        if( CurrentPosition[i] != 0 ) {
            int x1 = i % SQRT_BOARD_SIZE;
            int y1 = i / SQRT_BOARD_SIZE;
            for( int j = 0; j < BOARD_SIZE; ++j ) {
                if( CurrentPosition2[j] == CurrentPosition[i] ) {
                    int x2 = j % SQRT_BOARD_SIZE;
                    int y2 = j / SQRT_BOARD_SIZE;
                    result += abs( x2 - x1 ) + abs( y2 - y1 );
                    break;
                }
            }
        }
    }
    return result;
}

int Solver::ManhattanChange( PositionId position, char direction, int* EndPosition )
{
    int valuePosition = GetPos( 0, CurrentPosition );
    if( direction == L || direction == R ) {
        if( direction == L ) {
            valuePosition += right;
            if( GetPos( CurrentPosition[valuePosition], EndPosition ) % SQRT_BOARD_SIZE >= valuePosition % SQRT_BOARD_SIZE ) {
                return -1;
            }
            return 1;
        }
        if( direction == R ) {
            valuePosition += left;
            if( GetPos( CurrentPosition[valuePosition], EndPosition ) % SQRT_BOARD_SIZE <= valuePosition % SQRT_BOARD_SIZE ) {
                return -1;
            }
            return 1;
        }
    } else if( direction == U || direction == D ) {
        if( direction == U ) {
            valuePosition += down;
            if( GetPos( CurrentPosition[valuePosition], EndPosition ) / SQRT_BOARD_SIZE >= valuePosition / SQRT_BOARD_SIZE ) {
                return -1;
            }
            return 1;
        }
        if( direction == D ) {
            valuePosition += up;
            if( GetPos( CurrentPosition[valuePosition], EndPosition ) / SQRT_BOARD_SIZE <= valuePosition / SQRT_BOARD_SIZE ) {
                return -1;
            }
            return 1;
        }
    }
    assert( false );
    return 0;
}

void Solver::GetSuccessors( PositionId currentPosition )
{
    PositionId newPosition;
    numberOfSuccessors = 0;
    IntToPos( currentPosition, CurrentPosition );
    int zeroPosition = GetPos( 0, CurrentPosition );
    if( zeroPosition % SQRT_BOARD_SIZE != 0 ) {
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - 1] );
        newPosition = PosToInt( CurrentPosition );
        Direction[numberOfSuccessors] = L;
        Successors[numberOfSuccessors++] = newPosition;
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - 1] );
    }
    if( zeroPosition % SQRT_BOARD_SIZE != SQRT_BOARD_SIZE - 1 ) {
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + 1] );
        newPosition = PosToInt( CurrentPosition );
        Direction[numberOfSuccessors] = R;
        Successors[numberOfSuccessors++] = newPosition;
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + 1] );
    }
    if( zeroPosition / SQRT_BOARD_SIZE != 0 ) {
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - SQRT_BOARD_SIZE] );
        newPosition = PosToInt( CurrentPosition );
        Direction[numberOfSuccessors] = U;
        Successors[numberOfSuccessors++] = newPosition;
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition - SQRT_BOARD_SIZE] );
    }
    if( zeroPosition / SQRT_BOARD_SIZE != SQRT_BOARD_SIZE - 1 ) {
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + SQRT_BOARD_SIZE] );
        newPosition = PosToInt( CurrentPosition );
        Direction[numberOfSuccessors] = D;
        Successors[numberOfSuccessors++] = newPosition;
        swap( CurrentPosition[zeroPosition], CurrentPosition[zeroPosition + SQRT_BOARD_SIZE] );
    }
}

void Solver::AStarIteration( PositionId endPosition, vector<stack<Position>>& PositionsQ, int& qNumber, int& size, bool Way )
{
    PositionId currentPosition = PositionsQ[qNumber].top().position;
    int currentDistance = PositionsQ[qNumber].top().distance;
    int currentManhattan = PositionsQ[qNumber].top().manhattan;
    PositionsQ[qNumber].pop();
    --size;
    if( Way && currentDistance > ( PosToDirWay[currentPosition] >> 14 ) || !Way && currentDistance > PosToDirWay[currentPosition] / 64 % 256 ) {
        while( qNumber < MAX_DISTANCE + 1 && PositionsQ[qNumber].empty() ) {
            ++qNumber;
        }
        return;
    }

    int* EndPosition;
    if( Way == forward ) {
        EndPosition = this->EndPosition;
    } else {
        EndPosition = StartPosition;
    }
    GetSuccessors( currentPosition );

    for( int i = 0; i < numberOfSuccessors; ++i ) {
        IntToPos( Successors[i], CurrentPosition );
        int newDistance = currentDistance + 1;
        int newManhattan = currentManhattan + ManhattanChange( Successors[i], Direction[i], EndPosition );
        int newHeuristic = newManhattan + Conflicts( EndPosition );
        int successorDirWay = PosToDirWay[Successors[i]];
        //assert( newDistance + newHeuristic >= qNumber );
        if( newDistance + newHeuristic < minDistance ) {
            if( successorDirWay % 4 == 2 - Way ) {
                if( Way ) {
                    assert( newHeuristic <= successorDirWay / 64 % 256 );
                    if( newDistance + successorDirWay / 64 % 256 < minDistance ) {
                        minDistance = newDistance + successorDirWay / 64 % 256;
                        intersection = Successors[i];
                        for( int i = minDistance; i < MAX_DISTANCE + 1; ++i ) {
                            if( !PositionsQ1[i].empty() ) {
                                size1 -= PositionsQ1[i].size();
                                PositionsQ1[i] = stack<Position>();
                            }
                            if( !PositionsQ2[i].empty() ) {
                                size2 -= PositionsQ2[i].size();
                                PositionsQ2[i] = stack<Position>();
                            }
                        }
                    }
                    assert( successorDirWay >> 14 == 0 );
                    assert( successorDirWay / 16 % 4 == 0 );
                    PosToDirWay[Successors[i]] += ( newDistance << 14 ) + ( Direction[i] << 4 ) + 2;
                    assert( PosToDirWay[Successors[i]] % 4 == 3 );
                } else {
                    assert( newHeuristic <= successorDirWay >> 14 );
                    if( newDistance + ( successorDirWay >> 14 ) < minDistance ) {
                        minDistance = newDistance + ( successorDirWay >> 14 );
                        intersection = Successors[i];
                        for( int i = minDistance; i < MAX_DISTANCE + 1; ++i ) {
                            if( !PositionsQ1[i].empty() ) {
                                size1 -= PositionsQ1[i].size();
                                PositionsQ1[i] = stack<Position>();
                            }
                            if( !PositionsQ2[i].empty() ) {
                                size2 -= PositionsQ2[i].size();
                                PositionsQ2[i] = stack<Position>();
                            }
                        }
                    }
                    assert( successorDirWay / 64 % 256 == 0 );
                    assert( successorDirWay / 4 % 4 == 0 );
                    PosToDirWay[Successors[i]] += ( newDistance << 6 ) + ( Direction[i] << 2 ) + 1;
                    assert( PosToDirWay[Successors[i]] % 4 == 3 );
                }
            } else {
                if( Way && ( successorDirWay != 2 && successorDirWay >> 14 == 0 || newDistance < successorDirWay >> 14 ) ) {
                    PositionsQ[newDistance + newHeuristic].push( Position( Successors[i], newDistance, newManhattan ) );
                    if( newDistance + newHeuristic < qNumber ) {
                        qNumber = newDistance + newHeuristic;
                    }
                    ++size;
                    if( successorDirWay >> 14 == 0 ) {
                        PosToDirWay[Successors[i]] = ( newDistance << 14 ) + ( Direction[i] << 4 ) + 2;
                    } else {
                        if( successorDirWay % 4 == 3 && newDistance + successorDirWay / 64 % 256 < minDistance ) {
                            minDistance = newDistance + successorDirWay / 64 % 256;
                            intersection = Successors[i];
                            for( int i = minDistance; i < MAX_DISTANCE + 1; ++i ) {
                                if( !PositionsQ1[i].empty() ) {
                                    size1 -= PositionsQ1[i].size();
                                    PositionsQ1[i] = stack<Position>();
                                }
                                if( !PositionsQ2[i].empty() ) {
                                    size2 -= PositionsQ2[i].size();
                                    PositionsQ2[i] = stack<Position>();
                                }
                            }
                        }
                        PosToDirWay[Successors[i]] -= ( ( ( successorDirWay >> 14 ) - newDistance ) << 14 ) + ( ( successorDirWay / 16 % 4 - Direction[i] ) << 4 );
                    }
                } else if( !Way && ( successorDirWay != 1 && successorDirWay / 64 % 256 == 0 || newDistance < successorDirWay / 64 % 256 ) ) {
                    PositionsQ[newDistance + newHeuristic].push( Position( Successors[i], newDistance, newManhattan ) );
                    if( newDistance + newHeuristic < qNumber ) {
                        qNumber = newDistance + newHeuristic;
                    }
                    ++size;
                    if( successorDirWay / 64 % 256 == 0 ) {
                        PosToDirWay[Successors[i]] = ( newDistance << 6 ) + ( Direction[i] << 2 ) + 1;
                    } else {
                        if( successorDirWay % 4 == 3 && newDistance + ( successorDirWay >> 14 ) < minDistance ) {
                            minDistance = newDistance + ( successorDirWay >> 14 );
                            intersection = Successors[i];
                            for( int i = minDistance; i < MAX_DISTANCE + 1; ++i ) {
                                if( !PositionsQ1[i].empty() ) {
                                    size1 -= PositionsQ1[i].size();
                                    PositionsQ1[i] = stack<Position>();
                                }
                                if( !PositionsQ2[i].empty() ) {
                                    size2 -= PositionsQ2[i].size();
                                    PositionsQ2[i] = stack<Position>();
                                }
                            }
                        }
                        PosToDirWay[Successors[i]] -= ( ( successorDirWay / 64 % 256 - newDistance ) << 6 ) + ( ( successorDirWay / 4 % 4 - Direction[i] ) << 2 );
                    }
                }
            }
        }
    }
    while( qNumber < MAX_DISTANCE + 1 && PositionsQ[qNumber].empty() ) {
        ++qNumber;
    }
}

void ReadPosition( int* Position )
{
    for( int i = 0; i < BOARD_SIZE; ++i ) {
        cin >> Position[i];
    }
}

int main()
{
    Solver A;
    int distance = 0;
    string Route;
    int Position[BOARD_SIZE];
    ReadPosition( Position );
    A.InitStartPosition( Position );
    A.InitEndPosition();
    A.TwoWayAStar( distance, Route );

    cout << distance << endl;
    for( int i = 0; i < distance; ++i ) {
        if( Route[i] == 1 ) cout << 'R';
        if( Route[i] == 0 ) cout << 'L';
        if( Route[i] == 2 ) cout << 'U';
        if( Route[i] == 3 ) cout << 'D';
    }

    return 0;
}

