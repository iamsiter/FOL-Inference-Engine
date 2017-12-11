import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class homework {

	static Set<Statement> KB = new HashSet<Statement>();
	static HashMap<String, List<Statement>> predToStmtMap = new HashMap<String, List<Statement>>();
	static List<Statement> queryList =new ArrayList<Statement>();
	static int count = 0;
	public static void main(String[] args) throws IOException {
		BufferedReader bf = null;
		BufferedWriter bw = null;
		int queryCount, statementCount;
		String[] queries = null;
		String[] statements = null;
		Boolean[] result = null;
		try {
			bf = new BufferedReader(new FileReader(new File("input.txt")));
			String string = bf.readLine();
			queryCount = Integer.parseInt(string);
			queries = new String[queryCount];
			for (int i = 0; i < queryCount; i++) {// read all queries
				queries[i] = bf.readLine();
			}

			statementCount = Integer.parseInt(bf.readLine());
			statements = new String[statementCount];
			for (int i = 0; i < statementCount; i++) {// read the KB statements
				statements[i] = bf.readLine();
			}

			result = new Boolean[queryCount];

			preProcessStatements(statements);// Build KB and populate reverse mapping for predicate-->statements
			preProcessQueries(queries);
			
			int k=0;
			for (Statement query:queryList) {
				// Clone the predicate mapping
				Map<String, List<Statement>> predicateMapCopy = clonePredicateMap();

				// Clone the KB
				Set<Statement> KBWorkingSet = cloneKB();
				
				Boolean b = resolve(query, KBWorkingSet, predicateMapCopy);
				result[k++]=b;
			}

			bw = new BufferedWriter(new FileWriter("output.txt"));

			for (int i = 0; i < result.length; i++) {
				if (result[i]) {
					bw.write("TRUE\n");
					System.out.println("TRUE");
				} else {
					bw.write("FALSE\n");
					System.out.println("FALSE");
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			try {
				bf.close();
				bw.close();
			} catch (IOException e) {
				throw e;
			}
		}
	}
	
	private static void preProcessQueries(String[] queries) {
		for (String query : queries) {
			queryList.add(new Statement(query, Collections.singletonList(
					new Predicate(getPredicate(query), new LinkedList<String>(Arrays.asList(getArguments(query)))))));
		}
	}

	private static String complementStatement(String string) {
		return (string.charAt(0) != '~') ? "~" + string : string.substring(1);
	}
	
	private static Boolean resolve(Statement query, Set<Statement> KBWorkingSet, Map<String, List<Statement>> predMapWorkingCopy) {
		
		List<Statement> KBWorkingList=new LinkedList<Statement>(KBWorkingSet);

		query.setStatement(complementStatement(query.getStatement()));
		query.getPredicateList().get(0).setName(complementStatement(query.getPredicateList().get(0).getName()));
		
		// add negated query to KB
		KBWorkingSet.add(query);
		KBWorkingList.add(0,query);
		
		
		//System.out.println("-----------------------------------------");

		int sizeDiff = -1;
		while (true) {
			int size = KBWorkingList.size();
			for (int i = 0; i < KBWorkingList.size(); i++) {
				if (KBWorkingList.size() > 20000) {
					return false;
				}
				Statement statement = KBWorkingList.get(i);
				if (unify(statement, KBWorkingSet, KBWorkingList, predMapWorkingCopy)) {
					return true;
	            }
			}
			sizeDiff = KBWorkingList.size() - size;
			if (sizeDiff == 0) {
				break;
			}
		}
			
		return false;
	}

	private static boolean unify(Statement aStmt, Set<Statement> kBWorkingSet, List<Statement> kBWorkingList,
			Map<String, List<Statement>> predMapWorkingCopy) {
		//Check if aStmt is in the KB
		if(aStmt.getPredicateList().size()==1) {
			if(kBWorkingSet.contains(new Statement(complementStatement(aStmt.getStatement()))))
			   return true;
		}
				
		List<Predicate> aPredList=aStmt.getPredicateList();
		
		for (int i = 0; i < aPredList.size(); i++) {
			Predicate aPred=aPredList.get(i);
			Predicate bPred=null;
			String lookup = complementStatement(aPred.getName()).trim();
			List<Statement> bStmtList=predMapWorkingCopy.get(lookup);
			
			if (bStmtList != null) {//case  self statement: A(x)|B(y)|~A(y)
				if(bStmtList.contains(aStmt))
					continue;
			}
			
		if(bStmtList!=null) {
			for (int j = 0; j < bStmtList.size(); j++) {
				Statement bStmt = bStmtList.get(j);
                List<Predicate> bPredList=bStmt.getPredicateList();

				// Map to hold all the unification mappings
				HashMap<String, String> arg2ValueMap = null;
				
				boolean mayResolve = false;
				boolean willResolve = false;

				for (int m = 0; m < bPredList.size(); m++) {
				    bPred=bPredList.get(m);
					if (bPred.getName().equals(complementStatement(aPred.getName()))) {
						arg2ValueMap = new HashMap<String, String>();
						LinkedList<String> aArguments = aPred.getArguments();
						LinkedList<String> bArguments = bPred.getArguments();
						
						for (int k = 0; k < bArguments.size(); k++) {
							String aArg=aArguments.get(k).trim();
							String bArg=bArguments.get(k).trim();

							if (bArg.equals(aArg)) {
								if (isConstant(bArg))// [Joe-Joe]
									mayResolve = true;
								else
									mayResolve = false;
								arg2ValueMap.put(bArg,bArg);
								continue;
								} else {
									if (isConstant(aArg) && isConstant(bArg)) {// [Joe-Frank]
										willResolve = false;
										mayResolve = false;
										break;
									} else if (isConstant(aArg)) {// [Joe-*]

										if (arg2ValueMap.get(bArg) != null) {
											willResolve = false;
											break;
										}
										willResolve = true;
										arg2ValueMap.put(bArg, aArg);
									} else if (isConstant(bArg)) {// [*-Joe]
										if (arg2ValueMap.get(aArg) != null) {
											willResolve = false;
											break;
										}
										willResolve = true;
										arg2ValueMap.put(aArg, bArg);
									} else {// [x1-x2]
										if (arg2ValueMap.get(bArg) != null) {
											willResolve = false;
											break;
										}
										willResolve = true;
										arg2ValueMap.put(bArg, aArg);
                                    }
								}
						}
						if (willResolve) {
							break;
						} else if (mayResolve) {
							if (aPredList.size() == 1) {
							    willResolve = true;
								break;
							} else {
								continue;
							}
						}
					}
				}

				if (willResolve) {
			      	//A(x,y)|~B(Joe,y)    ------    B(x,Frank)|D(y,z)
					
					List<Predicate> newAPredList=new ArrayList<Predicate>(aPredList);
					List<Predicate> newBPredList=new ArrayList<Predicate>(bPredList);
					LinkedList<Predicate> masterList=new LinkedList<Predicate>();
					List<String> args=null;
					newAPredList.remove(aPred);
					newBPredList.remove(bPred);
					int aSize=newAPredList.size();
					int bSize=newBPredList.size();
					
					if (aSize == 0 && bSize == 0) {
						return true;
					} 
					
					Statement newStmt=new Statement();
					if(aSize!=0) {
                    for(int s=0;s<newAPredList.size();s++){
    					LinkedList <String> newArgList=new LinkedList<String>();
                        Predicate p=newAPredList.get(s);
						Predicate pCopy=new Predicate();
						pCopy.setName(p.getName());
						args=p.getArguments();
						for(String arg:args){
                            if (arg2ValueMap.get(arg) != null) {
						       newArgList.add(arg2ValueMap.get(arg));
							} else {
							   newArgList.add(arg);
							}	
				 		}
						pCopy.setArguments(newArgList);
					 	masterList.add(pCopy);
					  }	
				    }
					
                    if(bSize!=0) {
                       for(int s=0;s<newBPredList.size();s++){
                    		LinkedList <String> newArgList=new LinkedList<String>();
                    		Predicate p=newBPredList.get(s);
    						Predicate pCopy=new Predicate();
    						pCopy.setName(p.getName());
    						args=p.getArguments();
    						for(String arg:args){
                                if (arg2ValueMap.get(arg) != null) {
                                	newArgList.add(arg2ValueMap.get(arg));
    							} else {
    								newArgList.add(arg);
    							}	
                            }
    						pCopy.setArguments(newArgList);
    					 	masterList.add(pCopy);
    					  }	
                    }
					
                    newStmt.setPredicateList(masterList);
					
					List<Predicate> predList = newStmt.getPredicateList();
					
					//remove duplicates
					Set<Predicate> hs = new HashSet<Predicate>();
					hs.addAll(predList);
					predList.clear();
					predList.addAll(hs);

					/*// remove complements
					List<Predicate> toRemove = new ArrayList<Predicate>();
					for (Predicate pred : predList) {
						Predicate newPred = new Predicate();
						newPred.setName(complementStatement(pred.getName()));
						newPred.setArguments(new LinkedList<String>(pred.getArguments()));

						if (predList.contains(newPred)) {
							toRemove.add(pred);
						}
					}
					
					predList.removeAll(toRemove);
					if(predList.isEmpty())
						return true;*/
					
					newStmt.setPredicateList(predList);
					StringBuilder newStr=new StringBuilder();
					
					for(Predicate pred:predList) {
					  newStr.append(pred.name).append("(");
					  for(String arg:pred.getArguments()) {
					           newStr.append(arg).append(",");
					  }
					  newStr.setLength(newStr.length()-1);
					  newStr.append(")|");		  
					}
					if(newStr.length()>0)
					      newStr.setLength(newStr.length()-1);
					newStmt.setStatement(newStr.toString());
					
					//System.out.println("Resolving:::"+aStmt+"  &&  "+bStmt);

					if (kBWorkingSet.add(newStmt)) {
						//Add it to KB
						kBWorkingList.add(newStmt);
						//System.out.println("-->"+newStmt.getStatement());
						if (newStmt.getPredicateList().size() == 1) {
							if (kBWorkingSet.contains(new Statement(complementStatement(newStmt.getStatement())))) {
								return true;
							}
						}

						//Add to reverse pred map
						for (Predicate pr : newStmt.getPredicateList()) {
							String p=pr.getName();
							
							if (predMapWorkingCopy.get(p) != null) {
								predMapWorkingCopy.get(p).add(newStmt);
							} else {
								List<Statement> list = new ArrayList<Statement>();
								list.add(newStmt);
								predMapWorkingCopy.put(p, list);
							}
						}
					}
				}
			}
		  }
		}

		return false;
	}
	
	public static void preProcessStatements(String[] statements) {
		Predicate pred = null;
		for (String statement : statements) {
			statement=formatClause(statement);
			String tokens[] = statement.split("\\|");
			Statement stmt = new Statement();
            List<Predicate> predList=new ArrayList<Predicate>();  
			StringBuilder standStmt=new StringBuilder();			
            for (String token : tokens) {
				pred = new Predicate();
				pred.setName(getPredicate(token));
				standStmt.append(pred.getName()).append("(");
				String [] args=getArguments(token);
				for(int i=0;i<args.length;i++) {//standardizing step
					if(!isConstant(args[i].trim()))
					     args[i]=args[i]+(count);
					pred.getArguments().add(args[i].trim());
					standStmt.append(args[i].trim()).append(",");
				}
				standStmt.setLength(standStmt.length()-1);
				standStmt.append(")|");
			    predList.add(pred);
			}
            
			standStmt.setLength(standStmt.length()-1);
			stmt.setPredicateList(predList);
			stmt.setStatement(standStmt.toString());

			//populate reverse map
			for (Predicate p : predList) {
				if (predToStmtMap.get(p.getName().trim()) != null) {
					predToStmtMap.get(p.getName().trim()).add(stmt);
				} else {
					List<Statement> stmtList = new ArrayList<Statement>();
					stmtList.add(stmt);
					predToStmtMap.put(p.getName().trim(), stmtList);
				}
			}
						
			//populate KB
			KB.add(stmt);
			count++;
		}
	}
	
	private static String[] getArguments(String string) {
		string = string.split("\\(")[1].split("\\)")[0];
		return string.split(",");
	}

	private static boolean isConstant(String string) {
		if (isUpperCase(string.charAt(0))) {
			return true;
		}
		return false;
	}
	
	private static boolean isUpperCase(char c) {
		if (c >= 65 && c <= 90)
			return true;
		return false;
	} 
	
	private static String getPredicate(String query) {
		String[] split = query.split("\\(");
		return split[0].trim();
	}
	
	private static Map<String, List<Statement>> clonePredicateMap() {
		Map <String,List<Statement>> predicateMapCopy=new HashMap<String,List<Statement>>();
		Set<String> keys = predToStmtMap.keySet();
		for (String key : keys) {
			List<Statement> list = predToStmtMap.get(key);
			List<Statement> listClone = new ArrayList<Statement>();
			for (Statement item : list) {
				listClone.add(item);
			}
			predicateMapCopy.put(key, listClone);
		}
		return predicateMapCopy;
	}
	
	private static String formatClause(String clause) {
		String[] predicates = clause.split("\\|");
		String token = "";
		for (int j = 0; j < predicates.length; j++) {
			String predicate = predicates[j].trim();

			token = token + predicate;
			if (j != predicates.length - 1) {
				token = token + "|";
			}
		}
		return token;
	}
	private static Set<Statement> cloneKB() {
		Set<Statement> KBCopy = new HashSet<Statement>();
		for (Statement item : KB) {
			KBCopy.add(item);
		}
		return KBCopy;
	}
}



class Statement {
	public Statement(String statement) {
		this.statement = statement;
	}

	String statement;
	List<Predicate> predicateList=new ArrayList<Predicate>();
	
    Statement(){} 
	
	public Statement(String statement, List<Predicate> predicateList) {
		super();
		this.statement = statement;
		this.predicateList = predicateList;
	}

	public String toString() {
		return this.statement.trim();
	}
	
	public String getStatement() {
		return statement;
	}

	public void setStatement(String statement) {
		this.statement = statement;
	}

	public List<Predicate> getPredicateList() {
		return predicateList;
	}

	public void setPredicateList(List<Predicate> predicateList) {
		this.predicateList = predicateList;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((statement == null) ? 0 : statement.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Statement aStmt = (Statement) obj;
		if (statement == null) {
			if (aStmt.statement != null)
				return false;
		} 
		
		Statement bStmt=this;
		List<Predicate> aPredList=aStmt.getPredicateList();
		List<Predicate> bPredList=bStmt.getPredicateList();
	
		if(aPredList.size()!=bPredList.size())
			return false;
		
		int count=0;
		for(int i=0;i<aPredList.size();i++) {
			Predicate aPred=aPredList.get(i);
			for(int j=0;j<bPredList.size();j++) {
				Predicate bPred=bPredList.get(j);		
				if(aPred.equals(bPred)) {
					count++;
				}
			}
		}
		
		if(count==aPredList.size())
			return true;
		return false;
	}  
}

class Predicate {
	String name;
	LinkedList<String> arguments=new LinkedList<String>();
	
	public Predicate(){}
	
	public Predicate(String name, LinkedList<String> arguments) {
		super();
		this.name = name;
		this.arguments = arguments;
	}
	public String getName() {
		return name;
	}
	public void setName(String name) {
		this.name = name;
	}
	public LinkedList<String> getArguments() {
		return arguments;
	}
	public void setArguments(LinkedList<String> arguments) {
		this.arguments = arguments;
	}
	
	public String toString() {
		return this.name+"("+arguments+")";
	}	
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((arguments == null) ? 0 : arguments.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Predicate other = (Predicate) obj;
		if (arguments == null) {
			if (other.arguments != null)
				return false;
		}

		if (other.name.equals(this.name)) {
			List<String> aArgs=other.getArguments();
			List<String> bArgs=this.getArguments();
			boolean flag = true;
			if (aArgs.size() == bArgs.size()) {
				for (int i = 0; i < aArgs.size(); i++) {
					if (!aArgs.get(i).equals(bArgs.get(i))) {
						flag = false;
						break;
					}
				}
				return flag;
			}
			return false;
		}
		return false;
	}	
}